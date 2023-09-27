
object "Runtime" {
        code {
			// function round_up_to_mul_of_32(value) -> result {
            //     result := and(add(value, 31), not(31))
            //     // result := and(31, not(31))
            // }
            function foo1(x, y) -> result 
            {
                result := add(x,add(y, 1)) 
            }
            
            let x := 8

            let y := 3

            let z := foo1(x, y)

            y := 4

            mstore(0x40, z)
            
        }
    }
