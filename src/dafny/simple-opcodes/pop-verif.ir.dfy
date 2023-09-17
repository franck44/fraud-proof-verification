
include "../../../evm-dafny/src/dafny/state.dfy" 
include "../../../evm-dafny/src/dafny/evm.dfy"

include "yul-functions.dfy"

module VerifIR {

    import opened Int
    import opened Opcode
    import opened EvmState
    import EVM
    import opened Bytecode
    import Gas
    import opened Yul 

    // function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b(st: ExecutingState): (st': State)
    //     requires st.Capacity() >= 2
    //     ensures st'.IsRevert()
    // {
    //     revert(0, 0, st)
    // }

    // function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db(st: ExecutingState): (st': State) 
    //     requires st.Capacity() >= 2
    //     ensures st'.IsRevert()
    // {
    //     revert(0, 0, st)
    // }

    // function revert_error_3538a459e4a0eb828f1aed5ebe5dc96fe59620a31d9b33e41259bb820cae769f(st: ExecutingState): (st': State)  
    //     requires st.Capacity() >= 2
    //     ensures st'.IsRevert()
    // {
    //     revert(0, 0, st)
    // }

    /** Computes the smallest number larger than value and multiple of 32. 
     *  @param  value   The value to round up.
     *  @returns        The first multiple of 32 larger than value.
     *
     *  @todo: implement the computation with calls to /, add, and *
     */
    function {:verify false} round_up_to_mul_of_32(value: u256, st: ExecutingState): (r: (u256, State)) 
        requires st.Operands() >= 2
        requires st.Capacity() >= 2
        requires value as nat + 32 < TWO_256
        requires value == st.Peek(0)
        
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands()
        // ensures r.1.PC() == st.Peek(1) as nat
        ensures r.0 == r.1.Peek(0)
        ensures value < r.0 <= value + 32
        ensures r.0 % 32 == 0
    {
        var (r1, s1) := div1(value, 32, st);
        var (r2, s2) := add1(r1, 1, s1);
        var (r3, s3) := mul1(r2, 32, s2);
        assert s3.Peek(0) == (value / 32 + 1) * 32;

        // (r3, Yreturn(1, s3)) 
        (r3, s3)
    }

    // function Konst(value: u256, st: ExecutingState): ExecutingState 
    //     requires st.Capacity() >= 1
    // {
    //     Push32(st, value)
    // }

    // function Params()

    function {:verify false} test2(params: seq<u256>, st: ExecutingState): State
    {
        // compute (value / 32 + 1) * 32 on top of stack 
        // mul(add(div(value, 32), 1),32)
        // add(value, 32) 
        //  get the stack size 
        var k := st.Operands();
        //
        //   value is params[0] (top of stack)
        //  so params[i] is Peek(i)

        // params[0], 
        // 
        // Add(params[0], Konst(32, st)) 
        // 
        st
        // Mul(Add(Div()))
    } 

    /**
     *  Two arguments and one return address
     */
    // function finalize_allocation(memPtr: u256, size: u256, st: ExecutingState):(st': State) 
    //     requires st.Operands() >= 3
    //     requires memPtr == st.Peek(0)
    //     requires size == st.Peek(1)
    //     requires size as nat + 32 < TWO_256
    //     requires st.Capacity() >= 3

    //     ensures st'.EXECUTING?
    //     ensures st.Operands() == st'.Operands()
    // {
    //     //  We would have to stack a return address for the call to  round_up_to_mul_of_32
    //     //  We stack a dummy value for now
    //     // var s0 := Push32(st, 0);
    //     //  Make sure size if at the top of the stack
    //     //  For now we omit it and use structured calls ignoring the jump (call) and return (jump)

    //     //  put size at the top of the stack
    //     var s1 := Dup(st, 2);
    //     // assert s1.  [ size, memPtr, size ]
    //     var (result, s1) := round_up_to_mul_of_32(size, s1);
    //     // [ size, memPtr, round_up(size) ]
    //     //  [ size, memPtr, round_up(size), memPtr ]
    //     var (newFreePtr, s2) := add0(memPtr, result, Dup(s1, 2));
    //     //  [ size, memPtr, round_up(size) + memPtr ]
    //     assert newFreePtr == s2.Peek(0);
    //     assert memPtr == s2.Peek(1);
    //     // s2
    //     // var (lt1, s3) := lt();
    //     s2

    //     // st
    //             // let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
    //             // // protect against overflow
    //             // if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
    //             // mstore(64, newFreePtr)
    // }

    // function allocate_memory(size: u256, st: ExecutingState): (u256, State) 
    //     requires st.Capacity() >= 3
    //     requires st.Operands() >= 2
    //     requires size == st.Peek(0)
    //     requires st.MemSize() >= 64 + 32
    // {
    //     //  Get the free memory pointer in memPtr
    //     var (memPtr, st') := allocate_unbounded(st);
    //     (memPtr, st')
    //     //  Try to allocate round_up_to_mul_of_32(size) on top of memory pointer.
    //     // (memPtr, finalize_allocation(memPtr, size, st'))
    // }

    /** Get the free memory pointer. 
     */
    // function allocate_unbounded(st: ExecutingState): (r: (u256, State)) 
    //     requires st.Capacity() >= 1
    //     requires st.Operands() >= 1
    //     /** Memory size must be at least 64 (0x40) + 32.  */
    //     requires st.MemSize() >= 0x40 + 32
    //     ensures r.1.EXECUTING?
    //     ensures r.1.Operands() >= 1
    //     ensures r.0 == r.1.Peek(0) == st.Read(64)
    // {
    //     assume st.IsJumpDest(st.Peek(0));
    //     var st' := MLoad(Push1(st, 64));
    //     var r := st'.Read(64);
    //     //  Jump to return address 
    //     (r, Yreturn(1, st')) 
    // }

}