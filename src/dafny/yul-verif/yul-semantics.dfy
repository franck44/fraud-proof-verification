
// include "../../../evm-dafny/src/dafny/state.dfy"
include "../../../evm-dafny/src/dafny/util/int.dfy"

module Yul {

  import opened Int

  function add(x: u256, y: u256): u256
  {
    ((x as nat + y as nat) % TWO_256) as u256
  }

  function mstore(x: u256, y: u256): (u256, u256) 
  {
    (x, y)
  }

}