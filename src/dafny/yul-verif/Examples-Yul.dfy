
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

    const tag_1 := 0xf 

    const EX1_CODE := [
        PUSH1, 0x0a,
        PUSH1, 0x08,
        PUSH1, 0x03,
        SWAP1,
        PUSH1, 0x0f,
        JUMP,
        JUMPDEST,   //  tag_2 
        PUSH1, 0x40,
        MSTORE,
        STOP,
        JUMPDEST,   //  tag_1
        SWAP1,      
        PUSH1, 0x01, 
        ADD,
        ADD,
        SWAP1,
        JUMP
    ]

    function foo1(x: u256, y: u256): u256 
    {
        add(x, add(y, 1)) 
    }

    //  Let + mstore
    function foo2(): (u256, u256) 
    {
        var x := 8;
        var y := 3;
        var z := foo1(x, y);
        mstore(0x40, z)
    }

    function foo1EVM(st:ExecutingState): State
        requires st.Capacity() >= 2
        requires st.Operands() >= 2
        ensures foo1EVM(st).EXECUTING?
    {
        var s1 := Swap(st, 1);
        var s2 := Push1(s1, 0x1);
        Add(Add(s2))
        // swap + jump
    }

    function {:opaque} foo1EVMJump(st:ExecutingState): (st': State)
        requires st.Capacity() >= 2
        requires st.Operands() >= 3
        requires st.PC() == 0xf
        requires st.IsJumpDest(st.Peek(2))
        requires st.evm.code.contents == EX1_CODE

        ensures st'.EXECUTING?
        ensures st'.PC() == st.Peek(2) as nat
        ensures st'.Operands() == st.Operands() - 2  
    {
        var s0 := JumpDest(st);
        var s1 := Swap(st, 1);
        var s2 := Push1(s1, 0x1);
        var s3 := Add(Add(s2));
        Jump(Swap(s3, 1))
    }

     //  Let + mstore
    function foo2EVM(st:ExecutingState): State 
        requires st.Capacity() >= 4
        requires st.PC() == 0 
        ensures foo2EVM(st).EXECUTING?
    {
        // push tag_2
        var s2 := Push1(st, 0x08);
        var s3 := Push1(s2, 0x03);

        //  swap1 
        //  tag 1 
        //  jump
        var s4 := foo1EVM(s3);

        var s5 := Push1(s4, 0x40);
        var s6 := MStore(s5);
        //  stop()
        s6
    }

     //  Let + mstore
    function foo2EVMJump(st:ExecutingState): (st': State) 
        requires st.Capacity() >= 6
        requires st.PC() == 0 
        requires st.evm.code.contents == EX1_CODE
        // ensures foo2EVM(st).EXECUTING?
    {
        assert st.CodeAtPC() == PUSH1;
        var s1 := Push1(st, 0xa);
        var s2 := Push1(s1, 0x08);
        var s3 := Push1(s2, 0x03);

        var s4 := Push1(Swap(s3, 1), 0xf);
        
        assert s4.PC() == 0x9 as nat;
        assert Jump(s4).Peek(2) == 0xa;
        var s5 := foo1EVMJump(Jump(s4));

        // check return address
        assert s5.PC() == 0xa;

        var s6 := Push1(JumpDest(s5), 0x40);
        var s7 := MStore(s6);

        assert s7.PC() == 0xe;

        // assert Memory.ReadUint256(s7.evm.memory, 0x40 as nat) ==  0xc;
        // Stop(s6)
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
        // requires st.Operands() >= 2
        // requires st.Peek(0) == x 
        // requires st.Peek(1) == y 

        // ensures foo1EVM(st).Peek(0) == foo1(x, y)
    {
        var x := 8;
        var s1 := Push1(st, x as u8);

        var y := 3;
        var s2 := Swap(Push1(s1, y as u8), 1);

        var z := foo1(x, y);
        var s3 := foo1EVM(s2);

        assert s3.Peek(0) == z;

        //  tag_2 here 
        var s4 := MStore(Push1(s3, 0x40));
        assert s4.EXECUTING?;

        assert Memory.ReadUint256(s4.evm.memory, 0x40 as nat) == z;

        // st
        
    }

    // tag_ 1
    function {:opaque} equivFoo1(x: u256, y: u256, st: ExecutingState): (r:(u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 2
        ensures st.EXECUTING?
        requires st.Peek(0) == x 
        requires st.Peek(1) == y 

        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() - 1
        ensures r.1.Peek(0) == r.0
        // ensures r.0 == add(x,add(y, 1))
    {
        (foo1(x, y), foo1EVM(st))
    }

    function equivFoo2(st: ExecutingState): (r:(((u256, u256), State)))
        requires st.Capacity() >= 4
        ensures st.EXECUTING?

        ensures r.1.EXECUTING?
        ensures r.0.0  as nat + 31 < r.1.MemSize()
        ensures Memory.ReadUint256(r.1.evm.memory, r.0.0 as nat) == r.0.1

    {
        //  tag 2 
        var x, s1 := 8, Push1(st, 0x8);

        var y, s2 := 3, Swap(Push1(s1, 0x3), 1);

        assert s2.EXECUTING?;
        assert s2.Operands() >= 1;

        var (z, s3) := equivFoo1(x, y, s2);

        assert Push1(s3, 0x40).EXECUTING?;
        assert s3.Operands() >= 1;

        //  tag_2 here 
        var (v, s4) := (mstore(0x40, z), MStore(Push1(s3, 0x40)));
        assert s4.EXECUTING?;

        (v,  s4)

    }

}
