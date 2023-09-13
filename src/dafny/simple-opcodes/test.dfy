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
    //  need 96 bytes of argument (3 words)
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
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
    assert s3.Peek(0) == |calldata| as u256;
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
        Block_0x13_shift_right_224_unsigned(s7, selector, calldata)
    else 
        assert |calldata| < 4;
        assert s7.PC() == 0xe;
        Block_0xe_revert_error(s7)
}

/* 
// from 00000160
//  revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
00000039: JUMPDEST      //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize] 
0000003a: PUSH1 0x0     //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 0] 
0000003c: DUP1          //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 0, 0] 
0000003d: REVERT        //  revert(0,0)
*/
function {:opaque} Block_0x39_revert_error(st: ExecutingState):(st': State)
    requires st.PC() == 0x39
    requires st.Capacity() >= 2
    ensures st'.IsRevert()
{
    Revert(Dup(Push1(JumpDest(st), 0x0), 1))
}

/*

// from 00000141: JUMP          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize] jump to 0x3e
//  revert_error_3538a459e4a0eb828f1aed5ebe5dc96fe59620a31d9b33e41259bb820cae769f()
0000003e: JUMPDEST              //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize]
0000003f: PUSH1 0x0             //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 0]
00000041: DUP1                  //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 0, 0]
00000042: REVERT                //  revert(0,0)
*/
/** This code is unreachable. */
function {:opaque} Block_0x3e_revert_error(st: ExecutingState):(st': State)
    requires false
    requires st.PC() == 0x3e
    requires st.Capacity() >= 2
    ensures st'.IsRevert()
{
    Revert(Dup(Push1(JumpDest(st), 0x0), 1))
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
function Block_0x13_shift_right_224_unsigned(st: ExecutingState, ghost selector: u256, ghost calldata: Arrays.Array<u8>):(st': State) 
    requires st.PC() == 0x13
    requires st.Operands() >= 0
    requires st.Capacity() >= 18
    requires calldata == GetContext(st).callData
    requires |calldata| >= 4
    requires selector == U256.Shr(ByteUtils.ReadUint256(calldata, 0),0xe)
    ensures selector != 0x145ce24f ==> st'.IsRevert()
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
{
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x1e);
    var s3 := Push1(s2, 0x00);
    assert s3.Capacity() >= 2;
    var s4 := CallDataLoad(s3);
    assert s4.Peek(0) == ByteUtils.ReadUint256(calldata, 0);
    var s5 := Push2(s4, 0x2d);
    assert s5.Capacity() >= 1;
    // var s6 := Jump(s5); with jumps we need to prove that target is a jumpdest!!
    assume s5.IsJumpDest(0x2d);
    var s6 := Jump(s5);
    assert s6.EXECUTING?;
    assert s6.Capacity() >= 1;
    assert s6.Peek(1) ==  0x1e;
    assert s6.PC() == 0x2d;
    assert s6.Peek(0) == ByteUtils.ReadUint256(calldata, 0);
    Block_0x2d_shr(s6, selector, calldata)
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
function Block_0x1e_case_0x145ce24f(st: ExecutingState, ghost selector: u256, ghost calldata: Arrays.Array<u8> ):(st': State)
    requires st.Operands() >= 1
    requires st.Capacity() >= 17
    requires st.PC() == 0x1e
    requires calldata == GetContext(st).callData
    requires |calldata| >= 4
    requires selector == st.Peek(0)
    ensures selector != 0x145ce24f ==> st'.IsRevert()
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
{
    // assume st.Capacity() >= 7;
    var s1 := JumpDest(st);
    var s2 := Push4(s1,0x145ce24f);
    var s3 := Sub(s2);
    var s4 := Push2(s3, 0xe);
    assert s4.Capacity() >= 14;
    assume s4.IsJumpDest(0xe);
    assert s4.PC() == 0x28;
    var s5 := JumpI(s4);
    if s4.Peek(1) != 0 then 
        //  selector is different to 0x145ce24f => revert
        assert selector != 0x145ce24f;
        assert s5.PC() == 0xe;
        Block_0xe_revert_error(s5) 
    else 
        //  selector is 0x145ce24f => continue computation
        assert selector == 0x145ce24f;
        assert s5.PC() == 0x29;
        Block_0x29_case_0x145ce24f(s5, selector, calldata)
}

/*
00000029: PUSH2 0x191       //  [p, 0x191] and 0x145ce24f - calldataload[first 32 bytes] shr 0xe0 == 0
0000002c: JUMP              //  [p] jump top 0x191
*/
function Block_0x29_case_0x145ce24f(st: ExecutingState, ghost selector: u256, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x29 
    requires st.Operands() >= 0
    requires st.Capacity() >= 16
    requires calldata == GetContext(st).callData
    requires |calldata| >= 4
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
{
    var s1 := Push2(st, 0x191);
    assume s1.IsJumpDest(0x191);
    var s2 := Jump(s1);
    assert s2.PC() == 0x191;
    assert s2.Capacity() >= 16;
    Block_0x191(s2, calldata)
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
function Block_0x2d_shr(st: ExecutingState, ghost selector: u256, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x2d
    requires st.Operands() >= 2
    requires st.Peek(1) == 0x1e //  return address for shr(224, value)
    requires st.Capacity() >= 16
    requires calldata == GetContext(st).callData
    requires |calldata| >= 4
    requires selector == U256.Shr(ByteUtils.ReadUint256(calldata, 0),0xe)    
    requires ByteUtils.ReadUint256(calldata, 0) == st.Peek(0)
    ensures U256.Shr(st.Peek(0),0xe) != 0x145ce24f ==> st'.IsRevert()
    ensures selector != 0x145ce24f ==> st'.IsRevert()
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
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
    Block_0x1e_case_0x145ce24f(s5, selector, calldata)
}

/*
// function allocate_memory(size) -> memPtr {
                memPtr := allocate_unbounded()
                finalize_allocation(memPtr, size)
            }

0000008c: JUMPDEST      //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 0x109, 96]
0000008d: SWAP1         //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 96, 0x109]
0000008e: PUSH2 0x9f    //  
00000091: PUSH2 0x98    //  
00000094: PUSH2 0x33    //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 96, 0x109, 0x9f, 0x98, 0x33]
00000097: JUMP          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 96, 0x109, 0x9f, 0x98] jump to 0x33
*/
function Block_0x8c_allocate_memory(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x8c  
{
    st
}
/*
function abi_decode_t_struct$_StateProof_$8_memory_ptr(headStart, end) -> value {
                if slt(sub(end, headStart), 0x60) { revert_error_3538a459e4a0eb828f1aed5ebe5dc96fe59620a31d9b33e41259bb820cae769f() }
                value := allocate_memory(0x60)

                {
                    // stackHash

                    let offset := 0

                    mstore(add(value, 0x00), abi_decode_t_bytes32(add(headStart, offset), end))

                }

                {
                    // stackHashAfterPops

                    let offset := 32

                    mstore(add(value, 0x20), abi_decode_t_bytes32(add(headStart, offset), end))

                }

                {
                    // pops

                    let offset := 64

                    mstore(add(value, 0x40), abi_decode_t_uint256(add(headStart, offset), end))

                }

            }

// from 00000158
000000ef: JUMPDEST      //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0]
000000f0: SWAP2         //   [p, 0x1b8, 0x1a7, 4 + 0, calldatasize, 0x1a2]
000000f1: SWAP1         //   [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize]
000000f2: PUSH1 0x60    //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 96]
000000f4: DUP4          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 96, 4 + 0]
000000f5: DUP3          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 96, 4 + 0, calldatasize]
000000f6: SUB           //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 96, calldatasize - 4]
000000f7: SLT           //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, calldatasize - 4 < 96]
000000f8: PUSH2 0x13d   //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, calldatasize - 4 < 96, 0x13d]
000000fb: JUMPI         //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize] jump to 0x13d if calldatasize - 4 < 96 ==> and revert
*/
function Block_0xef_abi_decode_t_struct_StateProof_8_memory_ptr(st: ExecutingState,  ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0xef
    requires st.Operands() >= 3
    requires st.Peek(1) == |calldata| as u256 
    requires st.Peek(0) == 4
    requires st.Capacity() >= 10
    // requires calldata == GetContext(st).callData
    requires |calldata| >= 4 + 96
{
    var s1 := JumpDest(st);
    var s2 := Swap(s1, 2);
    var s3 := Swap(s2, 1);
    var s4 := Push1(s3, 0x60);
    var s5 := Dup(s4, 4);
    var s6 := Dup(s5, 3);
    assert s6.Peek(0) == |calldata| as u256;
    assert s6.Peek(1) == 4;
    var s7 := Sub(s6);
    assert s7.Peek(0) == |calldata| as u256 - 4;
    assert s7.Peek(1) == 96;
    //  use Lt instead of SLt as peek(0) >= peek(1)
    // var s8 := SLt(s7);
    var s8 := Lt(s7);
    assert s8.Peek(0) == 0;
    var s9 := Push2(s8, 0x13d);
    assume s9.IsJumpDest(0x13d);
    var s10 := JumpI(s9);
    // jumpI 
    if s9.Peek(1) != 0 then 
        //  This branch can never be taken
        assert false;
        assert s10.PC() == 0x13d;
        Block_0x13d(s10)
    else 
        assert s10.PC() == 0xfc;
        Block_0xfc(s10, calldata)
}

/* 
//  if slt(sub(end, headStart), 0x60) is true
000000fc: PUSH2 0x136   //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 0x136] 
000000ff: SWAP1         //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize] 
00000100: PUSH2 0x109   //  
00000103: PUSH1 0x60    //  
00000105: PUSH2 0x8c    //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 0x109, 96, 0x8c]
00000108: JUMP          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, 0x136, calldatasize, 0x109, 96] jump to 8c (allocate memory)
*/
function Block_0xfc(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0xfc
    requires st.Operands() >= 1
    requires st.Capacity() >= 3
{
    var s1 := Push2(st, 0x136);
    var s2 := Swap(s1, 1);
    var s3 := Push2(st, 0x109);
    var s4 := Push1(s3, 0x60);
    var s5 := Push2(s4, 0x8c);
    assume s5.IsJumpDest(0x8c);
    var s6 := Jump(s5);
    Block_0x8c_allocate_memory(s6, calldata)
}

/*

//  from fd 
0000013d: JUMPDEST      // [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize]
0000013e: PUSH2 0x3e    //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize, 0x3e]
00000141: JUMP          //  [p, 0x1b8, 0x1a7, 4 + 0, 0x1a2, calldatasize] jump to 0x3e (revert)

*/
/** This code is unreachable. */
function Block_0x13d(st: ExecutingState): (st': State) 
    requires false
    requires st.PC() == 0x13d
    requires st.Capacity() >= 2
{   
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x3e);
    assume s2.IsJumpDest(0x3e);
    var s3 := Jump(s2);
    Block_0x3e_revert_error(s3)
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
function Block_0x142(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x142
    requires st.Operands() >= 2
    requires st.Capacity() >= 11
    requires calldata == GetContext(st).callData
    requires |calldata| as u256 == st.Peek(1) >= 4
    requires 4 == st.Peek(0)
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
{
    var s1 := JumpDest(st);
    //  check that calldatasize() - 4 >= 96 = 32 + 32 + 32 (3 u256 values)
    var s2 := Swap(s1, 1);
    var s3 := Push1(s2, 0x60); // push 96
    var s4 := Dup(s3, 3);
    var s5 := Dup(s4, 3);
    var s6 := Sub(s5);
    assert s6.Peek(0) == |calldata| as u256 - 4;
    // var s7 := SLt(s6);
    //  @todo: why did the compiler insert a SLt??? and not a Lt?
    //  It looks like it does not know that |calldata| - 4 >= 0 and that's OK, but is
    //  the conversion to a signed comparison safe? Only of calldata 
    var s7 := Lt(s6);
    var s8 := Push2(s7, 0x15c);
    assume s8.IsJumpDest(0x15c);
    var s9 := JumpI(s8);
    // jumpI 
    if s8.Peek(1) != 0 then 
        assert |calldata| - 4 < 96;
        assert s9.PC() == 0x15c;
        Block_0x15c(s9, calldata)
    else 
        assert s9.PC() == 0x14e;
        assert |calldata| - 4 >= 96;
        Block_0x14e(s9, calldata)
}

/*
0000014e: PUSH2 0x159   //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize] and calldatasize - 4 >= 96
00000151: SWAP2         //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4]
00000152: PUSH1 0x0     //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4, 0]
00000154: ADD           //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0]  add(headStart, offset)
00000155: PUSH2 0xef    //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0, 0xef]
00000158: JUMP          //  [p, 0x1b8, 0x1a7, 0x1a2, calldatasize, 4 + 0] jump to 0xef call to abi_decode_t_struct$_StateProof_$8_memory_ptr(add(headStart, offset), dataEnd)
*/
function Block_0x14e(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x14e
    requires |calldata| - 4 >= 96
    // requires 
    requires st.Capacity() >= 11
    requires st.Operands() >= 2
    requires st.Peek(0) == |calldata| as u256
    requires st.Peek(1) == 4
{
    // assume st.Capacity() >= 11;
    var s1 := Push2(st, 0x159);
    var s2 := Swap(s1, 2);
    var s3 := Push1(s2, 0x0);
    var s4 := Add(s3);
    var s5 := Push2(s4, 0xef);
    assume s5.IsJumpDest(0xef);
    var s6 := Jump(s5);
    assert s6.Capacity() >= 10;
    Block_0xef_abi_decode_t_struct_StateProof_8_memory_ptr(s6, calldata)
}


/*
//  from 0000014d
0000015c: JUMPDEST      //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize]
0000015d: PUSH2 0x39    //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize, 0x39]
00000160: JUMP          //  [p, 0x1b8, 0x1a7, 0x1a2, 4, calldatasize] jump to 0x39
*/
function Block_0x15c(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State)
    requires st.PC() == 0x15c
    requires st.Capacity() >= 2
    ensures st'.IsRevert()
{
    var s1 := JumpDest(st);
    var s2 := Push2(s1, 0x39);
    assume s2.IsJumpDest(0x39);
    var s3 := Jump(s2);
    Block_0x39_revert_error(s3)
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
function Block_0x191(st: ExecutingState, ghost calldata: Arrays.Array<u8>):(st': State) 
    requires st.PC() == 0x191 
    requires st.Capacity() >= 16
    requires calldata == GetContext(st).callData
    requires |calldata| >= 4 
    ensures |calldata| - 4 < 96 ==> st'.IsRevert()
{
    //  prepare arguments to call and targets for computations
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
    assert s8.Capacity() >= 11;
    Block_0x142(s8, calldata)
}

   
}
