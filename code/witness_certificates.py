#!/usr/bin/env python3
"""Generate and independently verify non-residue witnesses for Brocard candidates."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
from bisect import bisect_right
from pathlib import Path

import numba
import numpy as np
import sympy


KNOWN = {4, 5, 7}


def sieve_primes(limit: int) -> list[int]:
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, int(sympy.integer_nthroot(limit, 2)[0]) + 1):
        if sieve[p]:
            sieve[p * p : limit + 1 : p] = b"\x00" * (((limit - p * p) // p) + 1)
    return [i for i, flag in enumerate(sieve) if flag]


def factorial_mod_wilson(n: int, q: int) -> int:
    tail = 1
    for value in range(n + 1, q):
        tail = (tail * value) % q
    return (-pow(tail, q - 2, q)) % q


def reference_witnesses(limit: int, primes: list[int]) -> np.ndarray:
    result = np.zeros(limit + 1, dtype=np.int64)
    for n in range(1, limit + 1):
        if n in KNOWN:
            continue
        index = bisect_right(primes, n)
        while index < len(primes):
            q = primes[index]
            residue = (factorial_mod_wilson(n, q) + 1) % q
            symbol = pow(residue, (q - 1) // 2, q) if residue else 0
            if symbol == q - 1:
                result[n] = q
                break
            index += 1
        if result[n] == 0:
            raise RuntimeError(f"prime search ceiling too low at n={n}")
    return result


@numba.njit(cache=True)
def mul_mod(a: int, b: int, modulus: int) -> int:
    # Current certified range is <= 10^6, so signed 64-bit multiplication is exact.
    return (a * b) % modulus


@numba.njit(cache=True)
def pow_mod(base: int, exponent: int, modulus: int) -> int:
    result = 1
    base %= modulus
    while exponent:
        if exponent & 1:
            result = mul_mod(result, base, modulus)
        base = mul_mod(base, base, modulus)
        exponent >>= 1
    return result


@numba.njit(cache=True)
def jacobi_symbol(a: int, n: int) -> int:
    a %= n
    result = 1
    while a:
        while (a & 1) == 0:
            a >>= 1
            r = n & 7
            if r == 3 or r == 5:
                result = -result
        a, n = n, a
        if (a & 3) == 3 and (n & 3) == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


@numba.njit(cache=True)
def native_witnesses(limit: int, primes: np.ndarray) -> np.ndarray:
    output = np.zeros(limit + 1, dtype=np.int64)
    prime_index = 0
    for n in range(1, limit + 1):
        if n == 4 or n == 5 or n == 7:
            continue
        while prime_index < primes.size and primes[prime_index] <= n:
            prime_index += 1
        index = prime_index
        while index < primes.size:
            q = int(primes[index])
            tail = 1
            for value in range(n + 1, q):
                tail = mul_mod(tail, value, q)
            factorial = (q - pow_mod(tail, q - 2, q)) % q
            residue = (factorial + 1) % q
            if jacobi_symbol(residue, q) == -1:
                output[n] = q
                break
            index += 1
    return output


def canonical_record(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("ascii")


def percentile(sorted_values: list[int], numerator: int, denominator: int) -> int:
    index = ((len(sorted_values) - 1) * numerator) // denominator
    return sorted_values[index]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1_000_000)
    parser.add_argument("--prime-margin", type=int, default=10_000)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--stats", type=Path, required=True)
    args = parser.parse_args()
    ceiling = args.limit + args.prime_margin

    # Independent prime enumerators are compared before witness generation.
    primes_a = [int(p) for p in sympy.primerange(2, ceiling + 1)]
    primes_b = sieve_primes(ceiling)
    assert primes_a == primes_b
    reference = reference_witnesses(args.limit, primes_a)
    native = native_witnesses(args.limit, np.asarray(primes_b, dtype=np.int64))
    if not np.array_equal(reference, native):
        mismatch = int(np.flatnonzero(reference != native)[0])
        raise AssertionError(f"implementations disagree at n={mismatch}")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    header = {
        "type": "header",
        "generator": "witness_certificates.py",
        "version": 1,
        "range": [1, args.limit],
        "known_solutions": sorted(KNOWN),
        "factorial_method": "Wilson complement",
    }
    with args.output.open("wb") as handle:
        handle.write(canonical_record(header) + b"\n")
        for n in range(1, args.limit + 1):
            q = int(reference[n])
            if n in KNOWN:
                payload: dict[str, object] = {"method": "known_solution", "n": n, "q": None}
            else:
                payload = {"method": "wilson", "n": n, "q": q}
            payload["sha256"] = hashlib.sha256(canonical_record(payload)).hexdigest()
            handle.write(canonical_record(payload) + b"\n")

    gaps = sorted(int(reference[n]) - n for n in range(1, args.limit + 1) if n not in KNOWN)
    max_gap = gaps[-1]
    max_gap_n = [n for n in range(1, args.limit + 1) if n not in KNOWN and int(reference[n]) - n == max_gap]
    stats = {
        "range": [1, args.limit],
        "records": args.limit,
        "witness_records": len(gaps),
        "known_solution_records": len(KNOWN),
        "gap_q_minus_n": {
            "min": gaps[0],
            "median_lower": percentile(gaps, 1, 2),
            "p90_lower": percentile(gaps, 9, 10),
            "p99_lower": percentile(gaps, 99, 100),
            "max": max_gap,
            "max_at_n": max_gap_n,
        },
        "implementations": [
            "CPython+SymPy primes+Euler criterion",
            "Numba-native+sieve+binary Jacobi",
        ],
        "versions": {
            "python": sys.version,
            "platform": platform.platform(),
            "sympy": sympy.__version__,
            "numpy": np.__version__,
            "numba": numba.__version__,
        },
    }
    stats["certificate_sha256"] = hashlib.sha256(args.output.read_bytes()).hexdigest()
    args.stats.write_text(json.dumps(stats, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(stats, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
