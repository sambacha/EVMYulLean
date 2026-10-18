# pragma version ^0.4.0
# Straight-line storage writes, no loop (corpus C3).
# Reference semantics: set(v) stores v; bump(d) adds d to x and reverts on overflow.
x: public(uint256)

@external
def set(v: uint256):
    self.x = v

@external
def bump(d: uint256):
    self.x += d
