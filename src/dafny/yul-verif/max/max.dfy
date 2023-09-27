
include "../../../../evm-dafny/src/dafny/state.dfy" 
include "../../../../evm-dafny/src/dafny/evm.dfy"

include "../yul-semantics.dfy"   

module maxYul { 

    import opened Int
    import opened Yul 
    import opened Opcode
    import opened EvmState
    import EVM
    import opened Bytecode 
    import Gas

    const tag_1: u8 := 0x0f
    const tag_2: u8 := 0x0a
    const tag_3: u8 := 0x1b
    const tag_4: u8 := 0x18


    method Max(x: u256, y: u256) returns (result: u256) 
        ensures result == x || result == y 
        ensures result >= x && result >= y 
    {
        result := x;
        if lt(x, y) > 0 {
            result := y;
        }
    }

    /**
     *  Prove that bytecode at tag1 returns same as Max.
     */
    method MaxProof(x: u256, y: u256, st:ExecutingState) returns (result: u256, s': State) 
        requires st.Operands() >= 3
        requires st.Peek(0) == x 
        requires st.Peek(1) == y 
        requires st.Peek(2) == tag_2 as u256
        requires st.IsJumpDest(st.Peek(2))
        requires st.PC() == tag_1 as nat 
        requires st.Capacity() >= 2

        ensures s'.EXECUTING?   
        ensures s'.PC() == tag_2 as nat 
        ensures s'.Operands() == st.Operands() - 2
        ensures s'.Peek(0) == result  
    {
        s' := AtTag1(st);
        result := x;
        if lt(x, y) > 0 {
            result := y;
        }

    }

     //  Let + mstore
    method Main() 
    {
        var x := 8;
        var y := 3;
        var z := Max(x, y);
        var _ := mstore(0x40, z);
    }

    method MainProof(st:ExecutingState) returns (z': u256, s': State) 
        requires st.Capacity() >= 5
        requires st.Operands() >= 0
        requires st.PC() == 0 as nat
        requires st.IsJumpDest(tag_2 as u256)
        
        ensures s'.EXECUTING?
        ensures s'.MemSize() > 0x40 + 31 
        ensures s'.Read(0x40) == z'
    {
        var x := 8;
        var y := 3;
        var s1 := AtPC0(st);

        var z, s2 := MaxProof(x, y, s1);
        assert z == s2.Peek(0);

        s' := AtTag2(s2);
        z':= z;
        
        var _ := mstore(0x40, z);
        //  check that mem store contains z 
        assert s'.Read(0x40) == z;
    }

   
    function AtPC0(st:ExecutingState): (s': State)
        requires st.Capacity() >= 5
        requires st.Operands() >= 0
        requires st.PC() == 0 as nat
        requires st.IsJumpDest(tag_2 as u256)

        ensures s'.EXECUTING?
        ensures s'.PC() == tag_1 as nat
    {
        /*
        00000000: PUSH1 0xa     //  tag_2 
        00000002: PUSH1 0x8
        00000004: PUSH1 0x3
        00000006: SWAP1
        00000007: PUSH1 0xf     //  tag_1 
        00000009: JUMP
        */
        var s1 := Push1(st, tag_2);
        var s2 := Push1(s1, 0x08);
        var s3 := Push1(s2, 0x03);
        var s4 := Swap(s3, 1);
        assert s4.Peek(2) == tag_2 as u256;
        var s5 := Push1(s4, tag_1);
        assume s5.IsJumpDest(tag_1 as u256);
        assert s5.Peek(3) == tag_2 as u256;
        assert s5.IsJumpDest(s5.Peek(3) as u256);
        var s6 := Jump(s5);
        s6
    }

    function AtTag2(st:ExecutingState): (s': State)
        requires st.Capacity() >= 1
        requires st.Operands() >= 0
        requires st.PC() == tag_2 as nat
    {
        /*
        0000000a: JUMPDEST
        0000000b: PUSH1 0x40
        0000000d: MSTORE
        0000000e: STOP
        */
        var s1 := JumpDest(st);
        var s2 := Push1(s1, 0x40);
        var s3 := MStore(s2);
        s3
    }

    function {:opaque} AtTag1(st:ExecutingState): (s': State)
        requires st.Capacity() >= 2
        requires st.Operands() >= 3
        requires st.PC() == tag_1 as nat
        requires st.IsJumpDest(st.Peek(2))
        requires st.Peek(2) == tag_2 as u256

        ensures s'.EXECUTING?
        ensures s'.Operands() == st.Operands() - 2  
        ensures s'.PC() == tag_2 as nat
        ensures s'.Peek(0) == if st.Peek(0) < st.Peek(1) then st.Peek(1) else st.Peek(0)
    {
        /*
        0000000f: JUMPDEST      //  tag_1 
        00000010: SWAP2
        00000011: SWAP1
        00000012: DUP1
        00000013: DUP4
        00000014: LT
        00000015: PUSH1 0x1b
        00000017: JUMPI
        */
        var s1 := JumpDest(st); //  r, y, x
        var s2 := Swap(s1, 2);  //  x, y, r 
        var s3 := Swap(s2, 1);  //  x, r, y
        var s4 := Dup(s3, 1);   //  x, r, y, y 
        var s5 := Dup(s4, 4);   //  x, r, y, y, x 
        assert s5.PC() == 0x14;
        var s6 := Lt(s5);       //  x, r, y, x < y
        assert s6.Peek(0) == if s5.Peek(0) < s5.Peek(1) then 1 else 0;
        var s7 := Push1(s6, tag_3); //  x, r, y, x < y, tag_ 3
        assert s7.Peek(1) == if st.Peek(0) < st.Peek(1) then 1 else 0;
        assume s7.IsJumpDest(tag_3 as u256);
        var s8 := JumpI(s7);        //  x, r, y 
        assert s8.Peek(0) == st.Peek(1);
        if s7.Peek(1) != 0 then
            assert st.Peek(0) < st.Peek(1);
            assert s8.PC() == tag_3 as nat;
            //  should return st.Peek(1)
            assert s8.Peek(1) == st.Peek(2); 
            assert s8.IsJumpDest(s8.Peek(1)); 
            var s' := AtTag3(s8);
            assert s'.Peek(0) == st.Peek(1);
            s'
        else 
            //  tag_4 
            assert st.Peek(0) >= st.Peek(1);
            //  should return st.Peek(0)
            assert s8.PC() == tag_4 as nat;
            AtTag4(s8)
    }

    function {:opaque} AtTag4(st:ExecutingState): (s': State)
        requires st.Operands() >= 3
        requires st.PC() == tag_4 as nat
        requires st.IsJumpDest(st.Peek(1))
        requires st.Peek(1) as nat == tag_2 as nat  

        ensures s'.EXECUTING?
        ensures s'.PC() == st.Peek(1) as nat == tag_2 as nat 
        ensures s'.Operands() == st.Operands() - 2 
        ensures s'.Peek(0) == st.Peek(2) 
    {
        /*
        00000018: JUMPDEST      // tag_4 x2, x1, x0 
        00000019: POP           //  x2, x1 
        0000001a: JUMP          //  x2 
        */
        var s9 := JumpDest(st);
        var s10 := Pop(s9);
        assert s10.IsJumpDest(s10.Peek(0));
        var s11 := Jump(s10);
        assert s11.PC() == st.Peek(1) as nat;
        s11
    }

    function {:opaque} AtTag3(st:ExecutingState): (s': State)
        requires st.Operands() >= 3
        requires st.Capacity() >= 1
        requires st.PC() == tag_3 as nat
        requires st.IsJumpDest(st.Peek(1))
        requires st.Peek(1) == tag_2 as u256

        ensures s'.EXECUTING?
        ensures s'.PC() == tag_2 as nat 
        ensures s'.Operands() == st.Operands() - 2
        ensures s'.Peek(0) == st.Peek(0)

    {
        /*
        0000001b: JUMPDEST      //  tag_ 3  x2, x1, x0 
        0000001c: SWAP1         //  x2, x0, x1 
        0000001d: SWAP2         //  x1, x0, x2 
        0000001e: POP           //  x1, x0 
        0000001f: SWAP1         //  x0, x1 
        00000020: PUSH0         //  x0, x1, 0 
        00000021: PUSH1 0x18    //  x0, x1, 0, 0x18 
        00000023: JUMP          //  x0, x1, 0
        */
        var s1 := JumpDest(st);
        var s2 := Swap(s1, 1);  
        var s3 := Swap(s2, 2);
        var s4 := Pop(s3);
        var s5 := Swap(s4, 1);
        var s6 := Push0(s5);
        var s7 := Push1(s6, tag_4);

        assume s7.IsJumpDest(tag_4 as u256);
        var s8 := Jump(s7);
        assert s8.Peek(0) == 0; //  x0, x1, 0 
        AtTag4(s8)
    }


    // function {:opaque} equivMax(x: u256, y: u256, st: ExecutingState): (r:(u256, State))
    //     requires st.Capacity() >= 2
    //     requires st.Operands() >= 3
    //     requires st.PC() == 0x0f
    //     requires st.IsJumpDest(st.Peek(2))

    //     requires st.Peek(0) == x 
    //     requires st.Peek(1) == y 

    //     ensures st.EXECUTING?
    //     ensures r.1.EXECUTING?
    //     ensures r.1.Operands() == st.Operands() - 2
    //     ensures r.1.Peek(0) == r.0
    // {
    //     (max(x, y), maxEVM(st))
    // }

    // // tag_ 1
    // method equivMax(x: u256, y: u256, st: ExecutingState) returns (result: u256, st': State)
    //     requires st.Capacity() >= 2
    //     requires st.Operands() >= 3
    //     requires st.PC() == 0x0f
    //     requires st.IsJumpDest(st.Peek(2))

    //     requires st.Peek(0) == x 
    //     requires st.Peek(1) == y 

    //     ensures st'.EXECUTING?
    //     ensures st'.Operands() >= 1 
    //     // == st.Operands() - 1 
    //     ensures st'.Peek(0) == result
    //     // ensures st'.PC() == st.Peek(2) as nat
    //     // ensures r.0 == add(x,add(y, 1))
    // {
    //     // var result := 0;
    //     var s1 := JumpDest(st);
    //     var s2 := Swap(s1, 1);
    //     var s3 := Dup(s2, 1);
    //     var s4 := Dup(s3, 3);
    //     // assert s4.Peek(0) == x;
    //     assert s4.Peek(1) == y;
    //     var s5 := Lt(s4);
    //     assert s5.Peek(1) == y;
    //     // assert s5.Peek(0) == if Lt(x, y) then 1 else 0;
    //     assert s5.Peek(0) == if lt(x, y) != 0 then 1 else 0;
    //     var s6 := Push1(s5, 0x1b);
    //     // assert s6.Peek(1) == s5.Peek(0);

    //     assume s6.IsJumpDest(s6.Peek(0));
    //     var s7 := JumpI(s6);

    //     if lt(x, y) > 0 {
    //         assert s6.Peek(1) != 0;
    //         assert s7.PC() == 0x1b;
    //         var result := y;
    //         assert result == s4.Peek(1);
    //         assert result == s7.Peek(0);
    //         assert s7.Peek(0) == st.Peek(1);
    //         var s8 := JumpDest(s7);
    //         var s9 := Push1(s8, 0x17);
    //         var s10 := Jump(s9);
    //         // return result, s7;
    //         // assert 
    //         // s7 := 
    //         // assert 
    //     } else {
    //         // assert s6.Peek(1) == 0;
    //         assert s7.PC() == 0x17;
    //         var s8 := JumpDest(s7);
    //         var s9 := Pop(s8);
    //         var s10 := Swap(s9, 1);
    //         assert s10.IsJumpDest(s10.Peek(0));
    //         result := x;
    //         assert result == s4.Peek(0);
    //         assert result == s10.Peek(1);
    //         assert s7.Peek(0) == st.Peek(1);
    //         return result, Jump(s10);
    //     }
    // }

    // function maxEVM(st:ExecutingState): (s': State)
    //     requires st.Capacity() >= 2
    //     requires st.Operands() >= 3
    //     requires st.PC() == 0x0f
    //     requires st.IsJumpDest(st.Peek(2))

    //     ensures s'.EXECUTING?
    //     ensures s'.Operands() >= 1
    //     // == st.Operands() + 1
    // {
    //     /*
    //     0000000f: JUMPDEST      //  tag_1 
    //     00000010: SWAP2
    //     00000011: SWAP1
    //     00000012: DUP1
    //     00000013: DUP4
    //     00000014: LT
    //     00000015: PUSH1 0x1b
    //     00000017: JUMPI
    //     */
    //     var s1 := JumpDest(st);
    //     var s2 := Swap(s1, 2);
    //     var s3 := Swap(s2, 1);
    //     var s4 := Dup(s3, 1);
    //     var s5 := Dup(s4, 4);
    //     var s6 := Lt(s5);
    //     var s7 := Push1(s6, tag_3);
    //     assume s7.IsJumpDest(tag_3 as u256);
    //     var s8 := JumpI(s7);

    //     if s6.Peek(1) != 0 then
    //         assert s7.PC() == tag_3;
    //         s7
    //     else 
    //         assert s7.PC() == 0x17;
    //         var s8 := JumpDest(s7);
    //         var s9 := Pop(s8);
    //         var s10 := Swap(s9, 1);
    //         assert s10.IsJumpDest(s10.Peek(0));
    //         Jump(s10)
    // }

   
}