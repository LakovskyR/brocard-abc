#!/usr/bin/env python3
"""Stream-verifier for Brocard witness JSONL files."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from functools import lru_cache
from pathlib import Path

from witness_certificates import canonical_record, factorial_mod_wilson


KNOWN = {4: 5, 5: 11, 7: 71}


@lru_cache(maxsize=None)
def is_prime_trial(q: int) -> bool:
    if q == 2:
        return True
    if q < 2 or q % 2 == 0:
        return False
    return all(q % divisor for divisor in range(3, math.isqrt(q) + 1, 2))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    count = 0
    expected_n = 1
    with args.certificate.open("rb") as handle:
        header = json.loads(handle.readline())
        assert header["type"] == "header"
        for raw_line in handle:
            record = json.loads(raw_line)
            digest = record.pop("sha256")
            assert hashlib.sha256(canonical_record(record)).hexdigest() == digest
            n = int(record["n"])
            assert n == expected_n
            expected_n += 1
            if n in KNOWN:
                assert record == {"method": "known_solution", "n": n, "q": None}
                m = KNOWN[n]
                assert math.factorial(n) + 1 == m * m
            else:
                q = int(record["q"])
                assert record["method"] == "wilson"
                assert q > n and q % 2 == 1
                # Trial division is independent of the generators' sieve and SymPy primality.
                assert is_prime_trial(q)
                residue = (factorial_mod_wilson(n, q) + 1) % q
                assert residue != 0
                assert pow(residue, (q - 1) // 2, q) == q - 1
                for earlier_q in range(max(3, n + 1), q):
                    if is_prime_trial(earlier_q):
                        earlier_residue = (factorial_mod_wilson(n, earlier_q) + 1) % earlier_q
                        earlier_symbol = pow(earlier_residue, (earlier_q - 1) // 2, earlier_q) if earlier_residue else 0
                        assert earlier_symbol != earlier_q - 1
            count += 1
    assert count == header["range"][1] - header["range"][0] + 1
    print(f"verified_records={count} file_sha256={hashlib.sha256(args.certificate.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
