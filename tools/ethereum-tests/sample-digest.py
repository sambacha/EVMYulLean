#!/usr/bin/env python3
"""Digest of the conformance sample, to compare runs byte for byte.

    python3 tools/ethereum-tests/sample-digest.py [tests_1.txt] [EthereumTests]

The sample is the one of docs/toolchain/UPGRADE_REVIEW.md: BlockchainTests/GeneralStateTests/
VMTests without vmPerformance, stMemoryTest, stRefundTest and stSStoreTest (1,707 Cancun tests at
ethereum/tests v14.1). The script keeps the lines of the phase-1 log (`lake exe conform`) whose
fixture file belongs to the sample, adds one empty line per kept line (the log writes a blank line
after every result), sorts, and prints the SHA-256 of the result joined by newlines.

Exit status: 0 if the digest equals EXPECTED (the value recorded on Lean 4.22, on 4.28 before the
map change, and after it), 1 if it differs, 2 on a usage error.
"""
import hashlib
import pathlib
import sys

EXPECTED = "14537cc205a86b01431655ffbb1fe1c5fc19355ec79035599789408f2f583442"
SAMPLE_DIRS = ["VMTests", "stMemoryTest", "stRefundTest", "stSStoreTest"]


def sample_files(corpus: pathlib.Path) -> set[str]:
    root = corpus / "BlockchainTests" / "GeneralStateTests"
    names = set()
    for d in SAMPLE_DIRS:
        for f in (root / d).rglob("*.json"):
            if "vmPerformance" not in f.parts:
                names.add(f.name)
    return names


def main() -> int:
    log = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "tests_1.txt")
    corpus = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else "EthereumTests")
    if not log.is_file() or not corpus.is_dir():
        print(f"usage: {sys.argv[0]} [tests_1.txt] [EthereumTests]", file=sys.stderr)
        return 2
    files = sample_files(corpus)
    lines = [l for l in log.read_text().split("\n") if l and l.split("[", 1)[0] in files]
    failed = [l for l in lines if not l.endswith(" - Success.")]
    digest = hashlib.sha256(("\n".join(sorted(lines + [""] * len(lines))) + "\n").encode()).hexdigest()
    print(f"sample: {len(lines)} tests, {len(failed)} not successful; sha256 {digest}")
    if digest != EXPECTED:
        print(f"digest differs from the recorded {EXPECTED}", file=sys.stderr)
        return 1
    print("identical to the recorded sample log")
    return 0


if __name__ == "__main__":
    sys.exit(main())
