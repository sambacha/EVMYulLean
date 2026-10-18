#!/usr/bin/env python3
"""Run calls on py-evm (Cancun) and report what a caller observes: an independent EVM oracle.

Called by `gen_vyper_fixtures.py` with the interpreter of a private virtual environment that has
py-evm installed. It reads one JSON request on stdin:

    {"code": "<hex>", "slot": <int>, "points": [{"data": "<hex>", "x0": <int>, "value": <int>}, ...]}

and prints one JSON list with, per point, `[success, gas_used, storage_after, output_hex]`.
With an optional `"slots": [<int>, ...]` in the request (used by the solc fixtures,
`tools/solc/gen_solc_fixtures.py`), `storage_after` is the list of those slots' values instead.

Each call is a single message call (`apply_message`), not a transaction: no intrinsic gas, no
refund, the same shape as the project's `Θ` frame. The contract sits at 0x1000 with storage
`{slot: x0}`, the caller at 0x2000 with balance 2^128, gas 5,000,000 (the Lean harness `budget`).
Every point runs on a fresh chain whose genesis holds the initial storage (see `run_point`).
"""

import json
import sys

from eth import constants
from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.cancun import CancunVM
from eth.vm.message import Message

CONTRACT = (0x1000).to_bytes(20, "big")
CALLER = (0x2000).to_bytes(20, "big")
BUDGET = 5_000_000


def run_point(code: bytes, slot: int, p: dict, slots: list | None = None) -> list:
    """One call on a fresh chain whose genesis already holds `{slot: x0}`.

    The genesis matters: EIP-2200 prices `SSTORE` from the slot's value at the start of the
    transaction ("original"). Writing `x0` into an existing state just before the call would leave
    the original at 0 and misprice every write. A fresh chain also makes every slot and address
    cold (EIP-2929), like the Lean harness, which passes `σ₀ = σ` and an empty substate to `Θ`.
    """
    chain_class = MiningChain.configure(__name__="VyperOracle",
                                        vm_configuration=((0, CancunVM),), chain_id=1)
    genesis = {"difficulty": 0, "gas_limit": 30_000_000, "timestamp": 0,
               "coinbase": constants.ZERO_ADDRESS, "extra_data": b"", "nonce": b"\x00" * 8,
               "mix_hash": constants.ZERO_HASH32}
    storage = {slot: p["x0"]} if p["x0"] else {}
    accounts = {CONTRACT: {"balance": 0, "nonce": 0, "code": code, "storage": storage},
                CALLER: {"balance": 2 ** 128, "nonce": 0, "code": b"", "storage": {}}}
    state = chain_class.from_genesis(AtomicDB(), genesis, accounts).get_vm().state
    msg = Message(gas=BUDGET, to=CONTRACT, sender=CALLER, value=p["value"],
                  data=bytes.fromhex(p["data"]), code=code)
    ctx = state.get_transaction_context_class()(gas_price=0, origin=CALLER)
    comp = state.computation_class.apply_message(state, msg, ctx)
    after = (state.get_storage(CONTRACT, slot) if slots is None
             else [state.get_storage(CONTRACT, k) for k in slots])
    return [comp.is_success, comp.get_gas_used(), after, comp.output.hex()]


def main() -> None:
    req = json.load(sys.stdin)
    code = bytes.fromhex(req["code"])
    json.dump([run_point(code, req["slot"], p, req.get("slots")) for p in req["points"]],
              sys.stdout)


if __name__ == "__main__":
    main()
