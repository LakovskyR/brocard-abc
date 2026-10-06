#!/usr/bin/env python3
"""Certify every Laishram-Shorey table cutoff with interval arithmetic."""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import sympy


ROWS = (
    (Fraction(3, 4), 14),
    (Fraction(7, 12), 49),
    (Fraction(6, 11), 72),
    (Fraction(1, 2), 127),
    (Fraction(34, 71), 175),
    (Fraction(5, 12), 548),
    (Fraction(1, 3), 6460),
)
THETA_COEFFICIENT = Fraction(1_000_081, 1_000_000)
INTERVAL_DIGITS = 50


def as_interval(value: Fraction | int) -> mp.iv.mpf:
    if isinstance(value, int):
        return mp.iv.mpf(value)
    return mp.iv.mpf(value.numerator) / value.denominator


def interval_bounds(value: mp.iv.mpf) -> dict[str, str]:
    lower, upper = value._mpi_
    return {
        "lower": mp.libmp.to_str(lower, INTERVAL_DIGITS),
        "upper": mp.libmp.to_str(upper, INTERVAL_DIGITS),
    }


def robbins_margin(n: int, exponent: Fraction) -> mp.iv.mpf:
    """L(n) - E*1.000081*n, where L is the Robbins lower bound."""
    x = mp.iv.mpf(n)
    e = as_interval(exponent)
    coefficient = as_interval(THETA_COEFFICIENT)
    return (
        mp.iv.mpf("0.5") * mp.iv.log(2 * mp.iv.pi * x)
        + x * mp.iv.log(x)
        - x
        + 1 / (12 * x + 1)
        - e * coefficient * x
    )


def size_threshold(exponent: Fraction) -> int:
    """Least S such that the certified margin is positive for every n >= S."""
    low, high = 1, 2
    while not robbins_margin(high, exponent).a > 0:
        low, high = high, 2 * high
    while low + 1 < high:
        middle = (low + high) // 2
        if robbins_margin(middle, exponent).a > 0:
            high = middle
        else:
            low = middle
    return high


def log_primorial(primes: list[int]) -> mp.iv.mpf:
    total = mp.iv.mpf(0)
    for prime in primes:
        total += mp.iv.log(prime)
    return total


def main() -> None:
    mp.iv.dps = INTERVAL_DIGITS
    rows = []
    for epsilon, omega_epsilon in ROWS:
        exponent = 2 * (1 + epsilon) / (1 - epsilon)
        threshold_prime = int(sympy.prime(omega_epsilon))
        primes = [int(p) for p in sympy.primerange(2, threshold_prime + 1)]
        assert len(primes) == omega_epsilon and primes[-1] == threshold_prime

        threshold = size_threshold(exponent)
        at_previous = robbins_margin(threshold - 1, exponent)
        at_threshold = robbins_margin(threshold, exponent)
        derivative_floor = mp.iv.log(threshold) - as_interval(exponent) * as_interval(THETA_COEFFICIENT)

        # The signs prove minimality. For x >= S,
        # f'(x) > log(x)-E*1.000081 >= log(S)-E*1.000081 > 0 because
        # 1/(2x)-12/(12x+1)^2 = (144x^2+1)/(2x(12x+1)^2) > 0.
        assert at_previous.b <= 0
        assert at_threshold.a > 0
        assert derivative_floor.a > 0

        cutoff = max(threshold_prime - 1, threshold - 1)
        rows.append(
            {
                "epsilon": f"{epsilon.numerator}/{epsilon.denominator}",
                "omega_epsilon": omega_epsilon,
                "threshold_prime_T": threshold_prime,
                "log_exact_threshold_primorial_interval": interval_bounds(log_primorial(primes)),
                "exponent_E": f"{exponent.numerator}/{exponent.denominator}",
                "size_threshold_S": threshold,
                "conditional_cutoff_N0": cutoff,
                "controlling_threshold": "prime" if threshold_prime >= threshold else "size",
                "certificates": {
                    "f_S_minus_1": interval_bounds(at_previous),
                    "f_S": interval_bounds(at_threshold),
                    "log_S_minus_E_times_1_000081": interval_bounds(derivative_floor),
                },
            }
        )

    best = min(rows, key=lambda row: int(row["conditional_cutoff_N0"]))
    report = {
        "assumption": "Baker explicit abc conjecture, Laishram-Shorey (2012), Conjecture 1.2",
        "method": {
            "factorial_lower_bound": "0.5*log(2*pi*n)+n*log(n)-n+1/(12*n+1)",
            "prime_product_upper_bound": "theta(n) < 1.000081*n",
            "interval_backend": f"mpmath.iv {mp.__version__}",
            "interval_decimal_digits": INTERVAL_DIGITS,
        },
        "rows": rows,
        "best_row": {
            "epsilon": best["epsilon"],
            "conditional_cutoff_N0": best["conditional_cutoff_N0"],
            "no_solution_for_n_at_least": int(best["conditional_cutoff_N0"]) + 1,
        },
    }
    output = Path(__file__).resolve().parents[1] / "outputs" / "abc_bound_table.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    payload = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("ascii")
    output.write_bytes(payload)
    print(f"{output.name} sha256={hashlib.sha256(payload).hexdigest()}")


if __name__ == "__main__":
    main()
