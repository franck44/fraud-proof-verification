
include "../../../evm-dafny/src/dafny/util/int.dfy"

module Yul {

  import opened Int

  /**
   *    Addition modulo 2^256.
   */
  function add(x: u256, y: u256): u256
  {
    ((x as nat + y as nat) % TWO_256) as u256
  }

  function mstore(x: u256, y: u256): (u256, u256)
  {
    (x, y)
  }

  /**
   *    Unsigned lower than.
   */
  function lt(x: u256, y: u256): u256
  {
    if x < y then 1 else 0
  }

}