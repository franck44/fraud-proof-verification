
object "Runtime" {
        code {
			// function round_up_to_mul_of_32(value) -> result {
            //     result := and(add(value, 31), not(31))
            //     // result := and(31, not(31))
            // }

            // The storage slot where the counter is stored
            // let slot := 0
            // The function selector
            let value := 2
            // round_up_to_mul_of_32(calldataload(0))
            
            // value
            // let value := calldataload(0)
            let x := 5
            //  value, 2
            //  2, value
            // 2, value, 2            

            let y := 3

            let x := 8

            // let a1 := y 
            // let a2 := add(a1,7)  
            // let a3 := add(a2,8) 
            // let a4 := add(a1,9) 
            // let a5 := add(a2,11) 
            // let a6 := add(a3,13) 
            // let a7 := add(a6,14) 
            // let a8 := add(a7,15) 
            // let a9 := add(a8,16) 
            // let a10 := add(a8, 20) 
            // let a11 := add(a1, 21) 
            // let a12 := add(a2, 22)  
            // let a13 := add(a5, 23) 
            // let a14 := add(a7, 24) 
            // let a15 := add(a1,a14)
            // let a16 := add(y, a15)
            
            //  let is the function eval(param) 
            //  2, value, 2 , 2 
            //  2, 2, 2, value
            //  add(value, x)
            //  2, 2, value + x(2) 
            //  value +x(2), 3, 2 
            //  add(x, y)
            //  value +x(2), 3 + 2
            //  mstore

            mstore(add(x,y), add(value, x))

            
        }
    }
/*
    add(x, y).add(value, x).mstore
    add(x,y).extract(value).extract(x).add.mstore
    extract(x).extract(y).add.extract(value).extract(x).add.mstore
    let(y).extract(x).extract(y).add.extract(value).extract(x).add.mstore
    let(value).let(x).let(y)
        .dup(x)              dup2
        .dup(y).add          
        .dup(value)
        .dup(x).
        add.mstore
*/
