/*
 * Copyright 2023 Franck Cassez.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */

include "../../../evm-dafny/src/dafny/state.dfy" 
include "../../../evm-dafny/src/dafny/evm.dfy"

import opened Int
import opened Opcode

/**
/
 *  Provide a proof for fraud prood verification of simple opcodes (stack).
 */
module Test {

    import opened Int
    import opened Opcode
    import opened EvmState
    import EVM
    import opened Bytecode
    import Gas


    //  extend functionality of state 
    /**
     *  This function should be provided in the State component.
     *  @todo   Add this function to State 
     *  Extract the Context of the call.
     */
    function GetContext(st: ExecutingState) : Context.T 
    {
        match st 
            case EXECUTING(s) => s.context 
    }
/*
/// @src 0:769:3600  "library VerifierHelper {..."
            mstore(64, memoryguard(128))

            let called_via_delegatecall := iszero(eq(loadimmutable("library_deploy_address"), address()))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x145ce24f
                {
                    // decodeAndVerifyStackProofForPOP(VerifierHelper.StateProof)

                    external_fun_decodeAndVerifyStackProofForPOP_45()
                }

                default {}
            }
*/
/*
// mstore(64, memoryguard(128))
00000000: PUSH1 0x80
00000002: PUSH1 0x40
00000004: MSTORE

// if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x145ce24f
                {
                    // decodeAndVerifyStackProofForPOP(VerifierHelper.StateProof)

                    external_fun_decodeAndVerifyStackProofForPOP_45()
                }

                default {}
            }

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

//                                                      iszero(lt(calldatasize(), 4))
*/
/*
//                                                      iszero(lt(calldatasize(), 4))
00000005: PUSH1 0x4     //  [p,4]   
00000007: CALLDATASIZE  //  [p,4, CALLDATASIZE]
00000008: LT            //  [p, (CALLDATASIZE < 4)?1:0]
00000009: ISZERO        //  [p, if CALLDATASIZE < 4 then 0 else 1]
0000000a: PUSH2 0x13    //  [p, if CALLDATASIZE < 4 then 0 else 1, 0x13]
0000000d: JUMPI         //   [p] jump to 0x13 if CALLDATASIZE >= 4
*/
function Main_0x00000005(st: ExecutingState, ghost selector: u256, ghost calldata: Arrays.Array<u8>):(st': State) 
    /** selector is first 4 bytes of calldata. */
    requires selector == U256.Shr(ByteUtils.ReadUint256(GetContext(st).callData, 0),0xe)
    /** calldata is the context calldata.  */
    requires calldata == GetContext(st).callData
    /** Stack is empty. */
    requires st.Operands() == 0
    /** Memory writes  permitted. */
    requires st.WritesPermitted()
    /** Initial pc is zero. */
    requires st.PC() == 0
    /** Property 1. If not enough calldata revert. Minimum is 4 bytes for the name of the function. */
    ensures |calldata| < 4 ==> st'.IsRevert()
    /** Property 2. If the selector is not the signature of the function, revert. */
    ensures selector != 0x145ce24f ==> st'.IsRevert()
{
    // mstore(64, memoryguard(128))
    var s1 := MStore(Push1(Push1(st, 0x80), 0x40));
    assert s1.EXECUTING? && s1.PC() == 0x05;
    // assert s1.Operands() >= 0;
    //  iszero(lt(calldatasize(), 4))
    var s2 := Push1(s1, 0x04);
    var s3 := CallDataSize(s2);
    assert s3.Peek(0) == GetContext(st).CallDataSize();
    var s4 := Lt(s3);
    var s5 := IsZero(s4);
    // assert s5.Operands() >= 1;
    var s6 := Push2(s5, 0x0013);
    //  if iszero(lt(calldatasize(), 4)) 
    assert s6.Operands() >= 2;
    //  JUMPI to shift_right_224_unsigned(calldataload(0)), need to assume that target is JumpDest
    assume s6.IsJumpDest(0x13);
    var s7 := JumpI(s6);
    if s6.Peek(1) != 0 then 
        assert |calldata| >= 4;
        //  JUMPI to shift_right_224_unsigned(calldataload(0)), need to assume that target is JumpDest
        assert s7.PC() == 0x13;
        Block_0x13_shift_right_224_unsigned(s7, calldata, |calldata|)
        // ghost var selector := s7.Peek(0);
    else 
        assert |calldata| < 4;
        assert s7.PC() == 0xe;
        Block_0xe_revert_error(s7)
}

/*
//  CALLDATASIZE < 4 -> revert                          //
// revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

0000000e: JUMPDEST
0000000f: PUSH2 0x1bc   //  [p, 0x1bc]
00000012: JUMP          //  [p]

*/
function {:opaque} Block_0xe_revert_error(st: ExecutingState):(st': State)
    requires st.Capacity() >= 2
    requires st.PC() == 0xe
    ensures st'.IsRevert()
{
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x1bc);
    assume s2.IsJumpDest(0x1bc);
    var s3 := Jump(s2);
    assert s3.GetStack() == st.GetStack();
    assert s3.PC() == 0x1bc;
    Block_0x1bc(s3)
}

/*
function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }
00000013: JUMPDEST      //  [p]
00000014: PUSH2 0x1e    //  [p, 0x1e] 
00000017: PUSH1 0x0     //  [p, 0x1e, 0]
00000019: CALLDATALOAD  //  [p, 0x1e, 0, calldataload[first 32 bytes at loc 0]]
0000001a: PUSH2 0x2d    //  [p, 0x1e, calldataload[first 32 bytes], 0x2d]
0000001d: JUMP          //  [p, 0x1e, calldataload[first 32 bytes]]
*/
function Block_0x13_shift_right_224_unsigned(st: ExecutingState, ghost initcalldata: Arrays.Array<u8>, ghost initcalldatasize: nat):(st': State) 
    requires st.PC() == 0x13
    requires st.Operands() >= 0
    requires st.Capacity() >= 12
    ensures U256.Shr(ByteUtils.ReadUint256(GetContext(st).callData, 0),0xe) != 0x145ce24f ==> st'.IsRevert()
{
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x1e);
    var s3 := Push1(s2, 0x00);
    assert s3.Capacity() >= 2;
    var s4 := CallDataLoad(s3);
    assert s4.Peek(0) == ByteUtils.ReadUint256(GetContext(st).callData, 0);
    var s5 := Push2(s4, 0x2d);
    assert s5.Capacity() >= 1;
    // var s6 := Jump(s5); with jumps we need to prove that target is a jumpdest!!
    assume s5.IsJumpDest(0x2d);
    var s6 := Jump(s5);
    assert s6.EXECUTING?;
    assert s6.Capacity() >= 1;
    assert s6.Peek(1) ==  0x1e;
    assert s6.PC() == 0x2d;
    assert s6.Peek(0) == ByteUtils.ReadUint256(GetContext(st).callData, 0);
    Block_0x2d_shr(s6)
}

/*
//  jump to compute shiftright and return after
//  swicth selector 
// case 0x145ce24f
                {
                    // decodeAndVerifyStackProofForPOP(VerifierHelper.StateProof)

                    external_fun_decodeAndVerifyStackProofForPOP_45()
                }
0000001e: JUMPDEST          //  [p, calldataload[first 32 bytes] shr 0xe0]
0000001f: PUSH4 0x145ce24f  //  [p, calldataload[first 32 bytes] shr 0xe0, 0x145ce24f]
00000024: SUB               //  [p, 0x145ce24f - calldataload[first 32 bytes] shr 0xe0]
00000025: PUSH2 0xe         //  [p, 0x145ce24f - calldataload[first 32 bytes] shr 0xe0, 0xe]
00000028: JUMPI             //  [p] and jump to 0xe (revert) if selector is not 0x145ce24f
*/
function Block_0x1e_case_0x145ce24f(st: ExecutingState):(st': State)
    requires st.Operands() >= 1
    requires st.Capacity() >= 9
    requires st.PC() == 0x1e
    ensures st.Peek(0) != 0x145ce24f ==> st'.IsRevert()
{
    // assume st.Capacity() >= 7;
    var s1 := JumpDest(st);
    var s2 := Push4(s1,0x145ce24f);
    var s3 := Sub(s2);
    var s4 := Push2(s3, 0xe);
    assert s4.Capacity() >= 6;
    assume s4.IsJumpDest(0xe);
    assert s4.PC() == 0x28;
    var s5 := JumpI(s4);
    if s4.Peek(1) != 0 then 
        //  selector is different to 0x145ce24f => revert
        assert s5.PC() == 0xe;
        Block_0xe_revert_error(s5) 
    else 
        //  selector is 0x145ce24f => continue computation
        assert s5.PC() == 0x29;
        Block_0x29_case_0x145ce24f(s5)
}

/*
00000029: PUSH2 0x191       //  [p, 0x191] and 0x145ce24f - calldataload[first 32 bytes] shr 0xe0 == 0
0000002c: JUMP              //  [p] jump top 0x191
*/
function Block_0x29_case_0x145ce24f(st: ExecutingState):(st': State)
    requires st.PC() == 0x29 
    requires st.Operands() >= 0
    requires st.Capacity() >= 8
{
    var s1 := Push2(st, 0x191);
    assume s1.IsJumpDest(0x191);
    var s2 := Jump(s1);
    assert s2.PC() == 0x191;
    assert s2.Capacity() >= 8;
    Block_0x191(s2)
}

/*
    Implementation of shift_right_224_unsigned
    newValue := shr(224, value)
0000002d: JUMPDEST      // [p, 0x1e, calldataload[first 32 bytes]]
0000002e: PUSH1 0xe0    // [p, 0x1e, calldataload[first 32 bytes], 0xe0] (e0 = 224)
00000030: SHR           // [p, 0x1e, calldataload[first 32 bytes] shr 0xe0] (extract 4 leftmost bytes of calldata)
00000031: SWAP1         // [p, calldataload[first 32 bytes] shr 0xe0, 0x1e]
00000032: JUMP          //  return to 0x1e
*/
function Block_0x2d_shr(st: ExecutingState):(st': State)
    requires st.PC() == 0x2d
    requires st.Operands() >= 2
    requires st.Peek(1) == 0x1e //  return address for shr(224, value)
    requires st.Capacity() >= 10
    // ensures st'.EXECUTING?
    // ensures st'.Operands() >= 1
    // ensures st'.Peek(0) == U256.Shr(st.Peek(0), 0xe)
    ensures U256.Shr(st.Peek(0),0xe) != 0x145ce24f ==> st'.IsRevert()
{
    var s1 := JumpDest(st);
    var s2 := Push1(s1, 0xe);
    var s3 := Shr(s2);
    assert s3.Peek(0) == U256.Shr(st.Peek(0),0xe);
    var s4 := Swap(s3, 1);
    assert s4.Peek(0) == 0x1e;
    assert s4.Peek(1) == U256.Shr(st.Peek(0),0xe);
    assume s4.IsJumpDest(0x1e);
    var s5 := Jump(s4);
    assert s5.PC() == 0x1e;
    Block_0x1e_case_0x145ce24f(s5)
}

/*
00000142: JUMPDEST      //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4]
// abi_decode_tuple_t_struct$_StateProof_$8_memory_ptr(4, calldatasize()) ?
00000143: SWAP1         //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize]
00000144: PUSH1 0x60    //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 96]
00000146: DUP3          //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 96, 4]
00000147: DUP3          //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 96, 4, calldatasize]
00000148: SUB           //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 96, calldatasize - 4]
00000149: SLT           //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, calldatasize - 4 < 96]  slt(sub(dataEnd, headStart), 96)
0000014a: PUSH2 0x15c   //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, calldatasize - 4 < 96, 0x15c]
0000014d: JUMPI         //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize] jump to 0x15c if calldatasize - 4 < 96
0000014e: PUSH2 0x159   //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize] and calldatasize - 4 >= 96
00000151: SWAP2         //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4]
00000152: PUSH1 0x0     //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4, 0]
00000154: ADD           //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0]  add(headStart, offset)
00000155: PUSH2 0xef    //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0, 0xef]
00000158: JUMP          //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0] jump to 0xef call to abi_decode_t_struct$_StateProof_$8_memory_ptr(add(headStart, offset), dataEnd) 

function abi_decode_tuple_t_struct$_StateProof_$8_memory_ptr(headStart, dataEnd) -> value0 {
        if slt(sub(dataEnd, headStart), 96) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

        {

            let offset := 0

            value0 := abi_decode_t_struct$_StateProof_$8_memory_ptr(add(headStart, offset), dataEnd)
        }

    }
*/
function Block_0x142(st: ExecutingState, calldatasize: u256):(st': State)
    requires st.PC() == 0x142
    requires st.Operands() >= 2
    requires st.Capacity() >= 3
    requires calldatasize == st.Peek(1)
{
    var s1 := JumpDest(st);
    //  chwck that calldatsize() - 4 >= 96 = 32 + 32 + 32 (3 u256 values)
    var s2 := Swap(s1, 1);
    var s3 := Push1(s2, 0x60); // push 96
    var s4 := Dup(s3, 3);
    var s5 := Dup(s4, 3);
    var s6 := Sub(s5);
    var s7 := SLt(s6);
    var s8 := Push2(s7, 0x15c);
    // jumpI 
    // if s4.Peek(1) != 0 then 
    //     //  selector is different to 0x145ce24f => revert
    //     assume s4.IsJumpDest(0xe);
    //     var s5 := JumpI(s4);
    //     assert s5.PC() == 0xe;
    //     Block_0xe_revert_error(s5) 
    // else 
    //     var s5 := Push2(s4, 0x191);
    //     assume s5.IsJumpDest(0x191);
    //     var s6 := Jump(s5);
    //     assert s6.PC() == 0x191;
    //     assert s6.Capacity() >= 8;
    //     Block_0x191(s6)
    s8
}

/*
// function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }
//  jump from calldatasize < 4
000001bc: JUMPDEST      //  prepare revert(0,0) [p]
000001bd: PUSH1 0x0     //  [p, 0]
000001bf: DUP1          //  [p, 0, 0]
000001c0: REVERT        //  revert(0,0) 

*/
function {:opaque} Block_0x1bc(st: ExecutingState):(st': State) 
    requires st.PC() == 0x1bc
    requires st.Capacity() >= 2
    ensures st'.IsRevert()
{
    Revert(Dup(Push1(JumpDest(st), 0x0), 1))
}

/*
//  selector is 0x145ce24f, extract calldata
// function external_fun_decodeAndVerifyStackProofForPOP_45() {

                let param_0 :=  abi_decode_tuple_t_struct$_StateProof_$8_memory_ptr(4, calldatasize())
                let ret_0 :=  fun_decodeAndVerifyStackProofForPOP_45(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint64__to_t_uint64__fromStack_library(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

00000191: JUMPDEST      //  [p]
00000192: PUSH2 0x1b8   //  [p, 0x1b8]
00000195: PUSH2 0x1a7   //  [p, 0x1b8, 0x1a7]
00000198: PUSH2 0x1a2   //  [p, 0x1b8, 0x1a7, 0x1a2]
0000019b: CALLDATASIZE  //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize]
0000019c: PUSH1 0x4     //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4]
0000019e: PUSH2 0x142   //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4, 0x142]
000001a1: JUMP          //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4]  jump to 0x142
*/
function Block_0x191(st: ExecutingState):(st': State) 
    requires st.PC() == 0x191 
    requires st.Capacity() >= 8
{
    //  prepare arguments to call and targets for computations
    // assume st.Capacity() >= 8 ;
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x1b8);
    var s3 := Push2(s2, 0x1a7);
    var s4 := Push2(s3, 0x1a2);
    var s5 := CallDataSize(s4);
    var s6 := Push1(s5, 0x04);
    var s7 := Push2(s6, 0x0142);
    assume s7.IsJumpDest(0x0142);
    var s8 := Jump(s7);
    assert s8.PC() == 0x142;
    assert s8.Capacity() >= 3;
    Block_0x142(s8, s8.Peek(1))
}

   
}
