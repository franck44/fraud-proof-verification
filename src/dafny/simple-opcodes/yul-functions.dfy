
include "../../../evm-dafny/src/dafny/state.dfy" 
include "../../../evm-dafny/src/dafny/evm.dfy"

module Yul {
    
    import opened Int
    import opened Opcode
    import opened EvmState
    import EVM
    import opened Bytecode
    import Gas

    datatype YulExpr = 
        |   Konst(v: u256) 
        |   Var(v: u256)
        |   YulAdd(a: YulExpr, b: YulExpr)

    datatype YulState = 
        YulState(s: State) 
        {
            predicate IsExecuting() {
                this.s.EXECUTING?
            } 

            function YPush32(a: u256): YulState 
                requires this.IsExecuting()
            {
                YulState(Push32(this.s, a))
            }

            // function foo(a: u8): string {
            //     a as string
            // }

            function ToBytecode(e: YulExpr): seq<u8> 
            {
                match e 
                    case Konst(v) => [Opcode.PUSH32, (v % 256) as u8] 

                    case Var(v) => [Opcode.DUP1]

                    case YulAdd(a, b) => 
                        var s1 := ToBytecode(b);
                        var s2 := ToBytecode(a);
                        s1 + s2 + [ADD]
            }

            function Execute(e: YulExpr): YulState 
                requires this.IsExecuting()
                requires e.Konst? || e.YulAdd?
            {
                match e 
                    case Konst(a) => this.YPush32(a)
                    case YulAdd(a, Konst(b')) => 
                        //  
                        this
                    case _ => this 
            }

            function KonstF(a: u256): YulState 
                requires this.s.EXECUTING?
                // requires this.s.Capacity() >= 1
            {
                YulState(Push32(this.s, a))
            }

            //  [b, a]
            // add(add(a, b), 1)

            // Push 1 / 1 [b, a, 1]
            // Dup 0 + 1 + 1 / 2    [b, a, 1, a]
            // Dup 1 + 2 / 3       [b, a, 1, a, b]
            // add [b, a, 1, a + b] / 2 
            //  add [b, a, a + b  + 1] / 1

            //  add(add(a, b), add(a,b))

            //  let e1 := add(a, b)
            //  let e2 := add(a, b)
            //  add(e1, e2)

            // [b, a]
            // [b, a, e1]
            // [b, a, e1, e2]
            // ...    

            // function add(a: u256, b : u256): YulState
            //     requires this.s.Capacity() >= 2 
            //     ensures add(a, b).EXECUTING?
            //     ensures add(a, b).Operands() >= 1
            //     ensures add(a, b).Peek(0) as nat == (a as nat + b as nat ) % TWO_256 as nat
            //     ensures add(a, b).Operands() == this.s.Operands() + 1
            //     ensures add(a, b).GetStack().contents[1..this.s.Operands() + 1] == this.s.GetStack().contents
            // {
            //     Add(Push32(Push32(this.s, b), a))
            // }

            function add1(a: YulExpr, b: YulExpr): (s': YulState)
                requires this.s.EXECUTING?
                requires b.Konst? || b.Var?
                requires a.Konst? || a.Var?
                requires a.Konst? || b.Konst?
                requires a.Var? && b. Var?
                // ensures s'.IsExecuting() ==> 
                //     s'.s.Operands()>= 1 && 
                //     s'.s.Peek(0) as nat == (a.v as nat + b.v as nat ) % TWO_256 as nat
                ensures  s'.IsExecuting() ==> 
                    s'.s.Operands() == this.s.Operands() + 1 

                ensures s'.IsExecuting() ==> 
                    s'.s.GetStack().contents[1..this.s.Operands() + 1] == this.s.GetStack().contents
            {
                match (a, b)
                    case (Konst(a'), Konst(b')) => 
                        //  stack b, code of a, add 
                        var s1 := this.KonstF(b');
                        if s1.IsExecuting() then 
                            var s2 := s1.KonstF(a');
                            if s2.IsExecuting() then 
                                YulState(Add(s2.s))
                            else s2
                        else s1
                    case (Konst(a'), Var(b')) => 
                        //  if b' is a var it is on the stack
                        //  we duplicate it to make sure we don't
                        //  modify the initial stack 
                        var s1 := YulState(Dup(this.s,1));
                        if s1.IsExecuting() then 
                            var s2 := s1.KonstF(a');
                            if s2.IsExecuting() then 
                                YulState(Add(s2.s))
                            else s2
                        else 
                            s1
                    case (Var(a'), Konst(b')) => 
                        //  Stack b' 
                        var s1 := this.KonstF(b');
                        //  retrieve Var(a'). 
                        //  it is not the second element on the stack
                        //  More generally, it is at index
                        //  1 + s1.Operands() - this.Operands()
                        if s1.IsExecuting() then 
                            var s2 := YulState(Dup(s1.s, s1.s.Operands() - this.s.Operands() + 1));
                            assert s1.s.Operands()  >= this.s.Operands();
                            if s2.IsExecuting() then 
                                YulState(Add(s2.s))
                            else s2
                        else 
                            s1
                    
                    case (Var(a'), Var(b')) => 
                        //  Stack b' (second on stack as second paraneter)
                        var s1 := YulState(Dup(this.s,2));
                        //  retrieve Var(a'). 
                        //  it is not the second element on the stack
                        //  More generally, it is at index
                        //  0 + s1.Operands() - this.Operands()
                        if s1.IsExecuting() then 
                            var s2 := YulState(Dup(s1.s, s1.s.Operands() - this.s.Operands() + 1));
                            assert s1.s.Operands()  >= this.s.Operands();
                            if s2.IsExecuting() then 
                                assert s2.s.Operands() == this.s.Operands() + 1;
                                assert s2.s.GetStack().contents[1..this.s.Operands() + 1] == this.s.GetStack().contents;
                                YulState(Add(s2.s))
                            else 
                                s2
                        else 
                            s1
            }

            // add(2, 1)
            //  Konst(1).Konst(2).ADD()

            // 2 + 3 + 1 from s  
            // add(add(1, 2), 3)

            //  push 3 push 2 push 1 add add 
            //  s.Konts(3).add(s.Konst(3),add(1, 2))
            //  s.Konst(3).add(1, 2).ADD()
            //  s.Konts(3).Konst(2).Konst(1).ADD().ADD() 
            //   
            //  add(value, 2)
            //  Konst(2).DUP2().ADD()
            //
            //  add(2, add(value, 3))
            //  "add(value, 3)".Konst(2).ADD()
            //  Konst(3).DUP2().ADD().Konst(2).ADD() 

            //  stack is ... value 
            // push 3 DUP2 ADD Push 2 ADD 
            // value (3 + value + 2)  

            // function add2(a: u256, s: ExecutingState): ExecutingState
            //     requires this.s.Capacity() >= 2 
            //     ensures add(a, b).EXECUTING?
            //     ensures add(a, b).Operands() >= 1
            //     ensures add(a, b).Peek(0) as nat == (a as nat + b as nat ) % TWO_256 as nat
            //     ensures add(a, b).Operands() == this.s.Operands() + 1
            //     ensures add(a, b).GetStack().contents[1..this.s.Operands() + 1] == this.s.GetStack().contents
            // {
            //     Add(Push32(Push32(this.s, a), b))
            // }
        }

    
    

    // function Konstant(value: u256, st: ExecutingState): ExecutingState 
    //     requires st.Capacity() >= 1
    // {
    //     Push32(st, value)
    // }

    /**
     *  Addition of the two top most stack elements.
     *  
     */
    // function YulAdd(e1: YulExpr, e2: YulExpr): (u256, State)
    //     requires e1.Konst? && e2.Konst?
    // {
    //     match (e1, e2) 
    //         case (Konst(c1), Konst(c2)) => 
    //             (c1 + c2, Add())


    // }

    /**
     * Push eight bytes onto stack.
     */
    function Push32(st: ExecutingState, k: u256) : (st': State) {
        PushN(st,32, k as u256)
    }

    /**
     *  Revert with two u8 values.
     */
    function revert(x: u8, y: u8, st: ExecutingState): (st': State)
        requires st.Capacity() >= 2
        ensures st'.IsRevert()
    {
        Revert(Push1(Push1(st, x), y))
    } 

    /**
     *  Simulate a return from a call.
     *  @param  k   The stack index that contains the return address.
     *  @param  st  The source state.
     */
    function Yreturn(k: nat, st:ExecutingState): (st': State)
        requires 1 <= k <= 16
        requires st.Operands() > k
        ensures st'.EXECUTING?
        ensures st'.Operands() == st.Operands() - 1 
    {
        assume st.IsJumpDest(st.Peek(k));
        Jump(Swap(st,k))
    }

    

    /**
     *  Addition of the two top most stack elements.
     */
    function add(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() + 1
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat + y as nat) % TWO_256 as nat) as u256

    {   
        var s1 := Push32(st, x);
        var s2 := Push32(s1, y);
        var s3 := Add(s2);
        (s3.Peek(0), s3)
    }

    /**
      *  Addition of the two top most stack elements.
      *     Add y to top of stack.
      */
    function add1(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 1
        requires st.Peek(0) == x

        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands()
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat + y as nat) % TWO_256 as nat) as u256

    {   
        var s2 := Push32(st, y);
        var s3 := Add(s2);
        (s3.Peek(0), s3)
    }

    /**
      *  Addition of the two top most stack elements.
      *     Add y to top of stack.
      */
    function add0(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 0
        requires st.Operands() >= 2
        requires st.Peek(0) == x
        requires st.Peek(1) == y

        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() - 1
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat + y as nat) % TWO_256 as nat) as u256

    {   
        // var s2 := Push32(st, y);
        var s3 := Add(st);
        (s3.Peek(0), s3)
    }

    /**
     *  Multiplication of the two top most stack elements.
     */
    function mul(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() + 1
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat * y as nat) % TWO_256 as nat) as u256

    {   
        var s1 := Push32(st, x);
        var s2 := Push32(s1, y);
        var s3 := Mul(s2);
        (s3.Peek(0), s3)
    }

    /**
     *  Multiplication of the two top most stack elements.
     Mul y to top of stack.
     */
    function mul1(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 1
        requires st.Peek(0) == x
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() 
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat * y as nat) % TWO_256 as nat) as u256

    {   
        var s2 := Push32(st, y);
        var s3 := Mul(s2);
        (s3.Peek(0), s3)
    }

    /**
     *  Multiplication of the two top most stack elements.
     Mul y to top of stack.
     */
    function mul0(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 1
        requires st.Peek(0) == x
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() 
        ensures r.1.Peek(0) == r.0
        ensures r.0 == ((x as nat * y as nat) % TWO_256 as nat) as u256

    {   
        var s2 := Push32(st, y);
        var s3 := Mul(s2);
        (s3.Peek(0), s3)
    }

    /**
     *  Division of the two top most stack elements.
     *  x / y
     */
    function div(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() + 1
        ensures r.1.Peek(0) == r.0
        ensures r.0 == if y == 0 then 0 else (x / y) as u256

    {   
        var s1 := Push32(st, y);
        var s2 := Push32(s1, x);
        var s3 := Bytecode.Div(s2);
        (s3.Peek(0), s3)
    }

    /**
     *  Division of the two top most stack elements.
     *  We can check that the topmost element is on the stack but that does not prevent
     *  an mistake. Best is to keep it as it and check that the result is actually 
     *  consitent with the inputs. 
     *  top / y
     */
    function div1(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 1
        requires st.Peek(0) == x

        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands()
        ensures r.1.Peek(0) == r.0
        ensures r.0 == if y == 0 then 0 else (x / y) as u256

    {   
        var s1 := Push32(st, y);
        var s2 := Swap(s1, 1);
        var s3 := Bytecode.Div(s2);
        (s3.Peek(0), s3)
    }

     /**
     *  Division of the two top most stack elements.
     *  We can check that the topmost element is on the stack but that does not prevent
     *  an mistake. Best is to keep it as it and check that the result is actually 
     *  consitent with the inputs. 
     *  top / y
     */
    function lt(x: u256, y: u256, st:ExecutingState): (r: (u256, State))
        requires st.Capacity() >= 2
        requires st.Operands() >= 1

        ensures r.1.EXECUTING?
        ensures r.1.Operands() == st.Operands() + 1
        ensures r.1.Peek(0) == r.0
        ensures r.0 == (if x < y then 1 else 0) as u256
    {   
        var s1 := Push32(st, y);
        var s2 := Push32(s1, x);
        var s3 := Lt(s2);
        (s3.Peek(0), s3)
    }

}