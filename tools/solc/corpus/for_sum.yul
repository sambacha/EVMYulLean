{
  let n := calldataload(0)
  let s := 0
  for { let i := 0 } lt(i, n) { i := add(i, 1) } { s := add(s, i) }
  sstore(0, add(s, 1))
}
