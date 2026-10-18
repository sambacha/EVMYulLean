{
  function g(a) -> r { r := add(a, mul(a, a)) }
  sstore(0, add(g(calldataload(0)), 1))
  sstore(1, add(g(calldataload(32)), 1))
}
