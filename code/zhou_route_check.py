#!/usr/bin/env python3
"""Brocard under Zhou (2025), arXiv:2503.14510v1, Theorem A1(i).

A1(i): coprime a + b = c with log|abc| >= 700 implies
    log|abc| <= 3 log rad(abc) + 8 sqrt(log|abc| log log|abc|).
For n! + 1 = m^2 take (a, b, c) = ((m-1)/2, 1, (m+1)/2): abc = n!/4 and rad(abc) = rad(n!),
so n is excluded when L = log(n!/4) >= 700 and L > 3 theta(n) + 8 sqrt(L log L).
Checked with interval arithmetic for 4 <= n <= 10^6 (exact theta, and theta(n) <= n log 4),
with a derivative-floor argument for the tails.

Run: python code/zhou_route_check.py [--verify-output]
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction
import sys
import time

import mpmath as mp


ROOT = Path(__file__).resolve().parents[1]
DIGITS = 60
ENDPOINT_PLACES = 70
LIMIT = 1_000_000
QUOTE = (
    "Theorem A1. Let (a, b, c) be a triple of non-zero coprime integers "
    "such that a + b = c.\n"
    "(i) Suppose that log(|abc|) >= 700, then we have\n"
    "log(|abc|) <= 3 log rad(abc) + 8 sqrt(log(|abc|) * log log(|abc|))."
)


def decimal_endpoint(raw: tuple[int, int, int, int], upper: bool) -> str:
    """Round an exact binary endpoint outwards using integer arithmetic."""
    sign, mantissa, exponent, _ = raw
    numerator = (-1 if sign else 1) * mantissa * 10**ENDPOINT_PLACES
    denominator = 1
    if exponent >= 0:
        numerator <<= exponent
    else:
        denominator <<= -exponent
    rounded = -((-numerator) // denominator) if upper else numerator // denominator
    prefix = "-" if rounded < 0 else ""
    digits = str(abs(rounded)).zfill(ENDPOINT_PLACES + 1)
    return prefix + digits[:-ENDPOINT_PLACES] + "." + digits[-ENDPOINT_PLACES:]


def bounds(value: mp.iv.mpf) -> dict[str, str]:
    lower, upper = value._mpi_
    return {
        "lower": decimal_endpoint(lower, False),
        "upper": decimal_endpoint(upper, True),
    }


def sieve(limit: int) -> bytearray:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            flags[p * p : limit + 1 : p] = b"\x00" * ((limit - p * p) // p + 1)
    return flags


def radical(number: int) -> int:
    result = 1
    p = 2
    while p * p <= number:
        if number % p == 0:
            result *= p
            while number % p == 0:
                number //= p
        p += 1
    return result * number


def tail_certificate(start: int, log4: mp.iv.mpf) -> dict:
    x = mp.iv.mpf(start)
    lower_L = x * mp.iv.log(x) - x + mp.iv.log(2 * mp.iv.pi * x) / 2 - log4
    slope_g = 1 - 4 * (mp.iv.log(lower_L) + 1) / mp.iv.sqrt(lower_L * mp.iv.log(lower_L))
    margin = lower_L - 3 * x * log4 - 8 * mp.iv.sqrt(lower_L * mp.iv.log(lower_L))
    derivative_floor = slope_g * mp.iv.log(x) - 3 * log4
    assert lower_L.a >= 700 and slope_g.a > 0
    assert margin.a > 0 and derivative_floor.a > 0
    return {
        "start_real_x": start,
        "factorial_lower_L": bounds(lower_L),
        "g_prime_at_lower_L": bounds(slope_g),
        "margin_lower_bound": bounds(margin),
        "derivative_floor": bounds(derivative_floor),
    }


def binary_fraction(raw: tuple[int, int, int, int]) -> Fraction:
    sign, mantissa, exponent, _ = raw
    value = Fraction((-1 if sign else 1) * mantissa)
    return value * 2**exponent if exponent >= 0 else value / 2**(-exponent)


def verify_output() -> None:
    """Check stored enclosures against exact products at higher precision."""
    data = json.loads((ROOT / "outputs" / "zhou_route.json").read_text(encoding="ascii"))
    mp.iv.dps = 90
    log4 = mp.iv.log(4)

    def contains(record: dict, value: mp.iv.mpf) -> None:
        lower, upper = map(binary_fraction, value._mpi_)
        assert Fraction(record["lower"]) <= lower <= upper <= Fraction(record["upper"])

    checked = 0
    for key, record in data["samples"].items():
        n = int(key)
        if n > 1039:
            continue
        # Trial division and integer products don't reuse the scan's sieve or sums.
        prime_numbers = [p for p in range(2, n + 1)
                         if all(p % d for d in range(2, math.isqrt(p) + 1))]
        L = mp.iv.log(math.factorial(n) // 4)
        theta = mp.iv.log(math.prod(prime_numbers))
        penalty = 8 * mp.iv.sqrt(L * mp.iv.log(L))
        for field, value in {
            "L": L, "theta": theta, "primorial_theta_bound": n * log4,
            "penalty": penalty, "exact_margin": L - 3 * theta - penalty,
            "primorial_margin": L - 3 * n * log4 - penalty,
        }.items():
            contains(record[field], value)
        checked += 1
    for tail in data["tails"].values():
        check = tail_certificate(tail["start_real_x"], log4)
        for field in ("factorial_lower_L", "g_prime_at_lower_L", "margin_lower_bound", "derivative_floor"):
            # New outward decimal endpoints also lie inside the stored enclosure.
            assert Fraction(tail[field]["lower"]) <= Fraction(check[field]["lower"])
            assert Fraction(check[field]["upper"]) <= Fraction(tail[field]["upper"])
    assert data["routes"]["exact"]["exclusion_runs"] == [[476, 478], [480, LIMIT]]
    assert data["routes"]["primorial"]["exclusion_runs"] == [[1039, LIMIT]]
    for route in data["routes"].values():
        assert route["excluded_count"] == sum(b - a + 1 for a, b in route["exclusion_runs"])
        assert route["excluded_count"] + route["not_excluded_count"] == LIMIT - 3
        assert route["unresolved_interval_count"] == 0
    L168 = mp.iv.log(math.factorial(168) // 4)
    assert L168.b < 700
    print(f"Verified {checked} sample rows using exact integer products at 90 digits; both tails pass.")
    print("L(168)=" + json.dumps(bounds(L168)))


def main() -> None:
    mp.iv.dps = DIGITS
    print(QUOTE, flush=True)
    primes = sieve(LIMIT)
    assert [n for n in range(2, 20) if primes[n]] == [2, 3, 5, 7, 11, 13, 17, 19]
    assert sum(primes) == 78_498
    log4 = mp.iv.log(4)
    factorial_log = mp.iv.mpf(0)
    theta = mp.iv.mpf(0)
    samples = {}
    known = []
    cases = {4: 5, 5: 11, 7: 71}
    sample_n = set(cases) | {169, 170, 476, 477, 478, 479, 480, 481, 1038, 1039, LIMIT}
    routes = {
        name: {
            "largest_n_not_excluded": None,
            "excluded_count": 0,
            "not_excluded_count": 0,
            "unresolved_interval_count": 0,
            "exclusion_runs": [],
        }
        for name in ("exact", "primorial")
    }
    minima = {name: None for name in routes}
    first_threshold = None
    previous_exact = None
    transitions = []
    started = time.perf_counter()
    for n in range(2, LIMIT + 1):
        logn = mp.iv.log(n)
        factorial_log += logn
        if primes[n]:
            theta += logn
        if n < 4:
            continue
        L = factorial_log - log4
        if L.a >= 700:
            eligible = True
            if first_threshold is None:
                first_threshold = n
        elif L.b < 700:
            eligible = False
        else:
            raise AssertionError(f"Unresolved size threshold at n={n}")
        penalty = 8 * mp.iv.sqrt(L * mp.iv.log(L))
        margins = {"exact": L - 3 * theta - penalty, "primorial": L - 3 * n * log4 - penalty}
        excluded_flags = {}
        for name, margin in margins.items():
            assert margin.a > 0 or margin.b <= 0, (name, n, bounds(margin))
            excluded = eligible and margin.a > 0
            excluded_flags[name] = excluded
            route = routes[name]
            if excluded:
                route["excluded_count"] += 1
                runs = route["exclusion_runs"]
                if runs and runs[-1][1] == n - 1:
                    runs[-1][1] = n
                else:
                    runs.append([n, n])
            else:
                route["not_excluded_count"] += 1
                route["largest_n_not_excluded"] = n
            cutoff = 480 if name == "exact" else 1039
            if n >= cutoff and (minima[name] is None or margin.a < minima[name][1].a):
                minima[name] = (n, margin)
        if n in sample_n:
            samples[str(n)] = {
                "is_prime": bool(primes[n]),
                "L": bounds(L),
                "theta": bounds(theta),
                "primorial_theta_bound": bounds(n * log4),
                "penalty": bounds(penalty),
                "exact_margin": bounds(margins["exact"]),
                "primorial_margin": bounds(margins["primorial"]),
                "L_at_least_700": eligible,
                "excluded": excluded_flags,
            }
        if previous_exact is not None and previous_exact != excluded_flags["exact"]:
            transitions.append({"n": n, "is_prime": bool(primes[n]), "excluded": excluded_flags["exact"]})
        previous_exact = excluded_flags["exact"]
        if n in cases:
            m = cases[n]
            a, b, c = (m - 1) // 2, 1, (m + 1) // 2
            fac = math.factorial(n)
            v2 = sum(n // (2**k) for k in range(1, n.bit_length() + 1))
            assert fac + 1 == m * m and m % 2 == 1
            assert a + b == c and math.gcd(a, c) == 1
            assert a * b * c == fac // 4 and v2 >= 3
            assert radical(a * b * c) == radical(fac)
            assert not eligible and all(v.b < 0 for v in margins.values())
            known.append({"n": n, "m": m, "triple": [a, b, c], "abc": a * b * c,
                          "v2_factorial": v2, "radical": radical(fac),
                          "exclusion_test_fails": True, "sample_key": str(n)})
        if n % 100_000 == 0:
            print(f"checked n={n}; last failures=" + str({k: v['largest_n_not_excluded'] for k, v in routes.items()}), flush=True)
    for name, route in routes.items():
        assert route["excluded_count"] + route["not_excluded_count"] == LIMIT - 3
        minimum_n, minimum_margin = minima[name]
        route["minimum_margin_after_final_cutoff"] = {"n": minimum_n, "margin": bounds(minimum_margin)}
        assert minimum_margin.a > 0
    assert routes["exact"]["largest_n_not_excluded"] == 479
    assert routes["primorial"]["largest_n_not_excluded"] == 1038
    tails = {
        "exact_beyond_scan": tail_certificate(LIMIT, log4),
        "primorial_from_1039": tail_certificate(1039, log4),
    }
    result = {
        "source": {"reference": "Z.-P. Zhou, arXiv:2503.14510v1 (2025), p. 2",
                   "theorem": "A1(i)", "quote_ascii_math_transcription": QUOTE,
                   "status": "Consequence conditional on the quoted statement; its proof was not audited."},
        "method": {"backend": "mpmath.iv", "version": mp.__version__, "decimal_digits": DIGITS,
                   "endpoint_decimal_places": ENDPOINT_PLACES, "endpoint_rounding": "outward, exact integer arithmetic on binary endpoints",
                   "range_inclusive": [4, LIMIT], "prime_count": sum(primes),
                   "factorial_log": "sum(log(k), k=2..n) with interval arithmetic",
                   "theta": "sum(log(p), prime p<=n) with integer Eratosthenes sieve",
                   "margin": "L - 3*T - 8*sqrt(L*log(L)); L=log(n!)-log(4)",
                   "exclusion": "L.lower>=700 and margin.lower>0",
                   "first_n_with_L_at_least_700": first_threshold},
        "known_solutions": known, "routes": routes, "samples": samples,
        "exact_exclusion_transitions": transitions, "tails": tails,
        "inputs_assumed": ["Zhou A1(i) as quoted; its proof is not checked here.",
                           "theta(n) <= n log 4, i.e. primorial(n) <= 4^n (Mathlib: primorial_le_4_pow).",
                           "log n! >= n log n - n + (1/2) log(2 pi n) (Robbins 1955)."],
    }
    output = ROOT / "outputs" / "zhou_route.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="ascii")
    print(json.dumps({"cutoffs": {name: route["largest_n_not_excluded"] for name, route in routes.items()},
                      "first_L_700": first_threshold, "exact_transitions": transitions,
                      "tails": tails, "seconds": round(time.perf_counter() - started, 2)}, indent=2), flush=True)
    print(f"{output.name} sha256={hashlib.sha256(output.read_bytes()).hexdigest()}", flush=True)


if __name__ == "__main__":
    if sys.argv[1:] == ["--verify-output"]:
        verify_output()
    elif sys.argv[1:]:
        raise SystemExit("Usage: python code/zhou_route_check.py [--verify-output]")
    else:
        main()
