# pragma version ^0.4.0
# Bounded loop calling an internal function, accumulating in memory (corpus C2).
# Reference semantics: run(n) stores and returns the sum of i*i for i in [0, n); reverts if n > 20.
total: public(uint256)

@internal
@pure
def _sq(a: uint256) -> uint256:
    return a * a

@external
def run(n: uint256) -> uint256:
    acc: uint256 = 0
    for i: uint256 in range(n, bound=20):
        acc += self._sq(i)
    self.total = acc
    return acc
