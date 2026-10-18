# pragma version ^0.4.0
# Bounded loop with a branch and a storage write in the body (docs/VYPER_V1_PLAN.md, corpus C1).
# Reference semantics: f(n) adds every i in [4, n) to x; reverts if n > 50 or the sum overflows.
x: public(uint256)

@external
def f(n: uint256):
    for i: uint256 in range(n, bound=50):
        if i > 3:
            self.x += i
