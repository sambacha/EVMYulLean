{
  function tri(n) -> r { r := n if gt(n, 0) { r := add(n, tri(sub(n, 1))) } }
  sstore(0, add(tri(calldataload(0)), 1))
}
