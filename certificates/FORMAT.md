# Witness certificate format

File: `certificates/witnesses_<lo>_<hi>.jsonl`. UTF-8, one JSON object per line, sorted keys,
compact separators, no trailing spaces.

Line 1, header:
{"factorial_method":"Wilson complement","generator":"<script>","known_solutions":[4,5,7],
 "range":[lo,hi],"type":"header","version":1}

Lines 2..: one record per n in [lo, hi], in order, no gaps:
{"method":"wilson","n":<int>,"q":<int>,"sha256":"<hex>"}
{"method":"known_solution","n":<int>,"q":null,"sha256":"<hex>"}   for n in {4,5,7}

Meaning of a "wilson" record: q is the smallest ODD prime q > n such that n! + 1 is a
quadratic non-residue modulo q. This certifies that n! + 1 is not a square. The prime 2 is
never a witness (every residue is a square mod 2) and must be skipped by verifiers.

sha256: hex SHA-256 of the canonical JSON of the record without the sha256 field
(sorted keys, separators "," and ":", ASCII).

Verification contract for any independent checker, per record:
1. n is the expected next integer; q is an odd prime > n (own primality test).
2. n! mod q computed by any method; residue r = (n! + 1) mod q; r != 0 and
   r^((q-1)/2) = q - 1 mod q.
3. Minimality: no odd prime p with n < p < q satisfies step 2.
4. Header range matches the record count; file SHA-256 matches the stats file.

Reference implementation: code/verify_certificates.py. The Lean checker in
lean/Brocard/Witness.lean verifies records 8..1038 in the kernel.
