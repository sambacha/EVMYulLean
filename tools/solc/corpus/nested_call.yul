{
  function inc(a) -> r { r := add(a, 1) }
  let n := calldataload(0)
  let s := 0
  for { let i := 0 } lt(i, n) { i := inc(i) } {
    for { let j := 0 } lt(j, i) { j := add(j, 1) } { s := add(s, j) }
  }
  sstore(0, add(s, 1))
}
