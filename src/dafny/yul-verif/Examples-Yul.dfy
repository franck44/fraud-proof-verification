

include "../../../evm-dafny/src/dafny/state.dfy" 
include "../../../evm-dafny/src/dafny/evm.dfy"

include "yul-semantics.dfy"

module ExamplesYul {

    import opened Int
    import opened Yul 
    import opened Opcode
    import opened EvmState
    import EVM
    import opened Bytecode
    import Gas

    function foo1(x: u256, y: u256): u256 
    {
        add(x, add(y, 1)) 
    }

    //  Let + mstore
    function foo2(): (u256, u256) 
        /*
        00000000: PUSH1 0xa
        00000002: PUSH1 0x8
        00000004: PUSH1 0x3
        00000006: SWAP1
        00000007: PUSH1 0xf
        00000009: JUMP
        */
    {
        var x := 8;
        var y := 3;
        var z := foo1(x, y);
        mstore(0x40, z)
    }

    function foo1EVM(st:ExecutingState): State
        requires st.Capacity() >= 2
        requires st.Operands() >= 2
        ensures st.EXECUTING?
        /*
        0000000f: JUMPDEST
        00000010: SWAP1
        00000011: PUSH1 0x1
        00000013: ADD
        00000014: ADD
        00000015: SWAP1
        00000016: JUMP
        */
    {
        var s1 := Swap(st, 1);
        var s2 := Push1(s1, 0x1);
        Add(Add(s2))
    }

     //  Let + mstore
    function foo2EVM(st:ExecutingState): State 
        requires st.Capacity() >= 4
        ensures foo2EVM(st).EXECUTING?
        ensures foo2EVM(st).EXECUTING?

        /*
        00000000: PUSH1 0xa
        00000002: PUSH1 0x8
        00000004: PUSH1 0x3
        00000006: SWAP1
        00000007: PUSH1 0xf
        00000009: JUMP
        */
    {
        var s2 := Push1(st, 0x8);
        var s3 := Push1(s2, 0x3);

        var s4 := foo1EVM(s3);
        // proofFoo1()
        var s5 := Push1(s4, 0x40);
        var s6 := MStore(s5);
        s6
    }

    lemma proofFoo1(x: u256, y: u256, st:ExecutingState)
        requires st.Capacity() >= 2
        requires st.Operands() >= 2
        requires st.Peek(0) == x 
        requires st.Peek(1) == y 

        ensures foo1EVM(st).Peek(0) == foo1(x, y)
    {
        //  Thanks Dafny
    }

    lemma proofFoo2(st:ExecutingState)
        requires st.Capacity() >= 4
        requires st.MemSize() == 0

        ensures foo2EVM(st).EXECUTING?
        ensures foo2().0 as nat + 31 < foo2EVM(st).MemSize()
        ensures Memory.ReadUint256(foo2EVM(st).evm.memory, foo2().0 as nat) == foo2().1   
    {
        //  Thanks Dafny
        // proofFoo1();
    }

    

}
