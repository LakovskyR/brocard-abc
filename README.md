# Brocard's equation under explicit abc

Brocard's problem asks for all solutions of

$$n! + 1 = m^2, \qquad n, m \in \mathbb{N}.$$

The known solutions are $n = 4, 5, 7$ $(m = 5, 11, 71)$. Whether others exist is open.

This repository contains a conditional proof that there are no others, with an explicit cutoff
$n \le 1038$ for the finite part, a certificate excluding $8 \le n \le 1038$ and a Lean 4
formalization of the whole argument from two named hypotheses.

## Prior work

Overholt [Ov] showed that the abc conjecture implies finitely many solutions. The explicit
conditional statement is also known. Laishram and Shorey [LS, Theorem 1, eq. (2)] show
that Baker's explicit abc conjecture [Ba; LS, Conjecture 1.2] implies $c < \mathrm{rad}(abc)^{7/4}$
for every coprime triple $a + b = c$. Browkin [Br, Theorem 6.1] shows that his hypothesis
$abc(1.8)$ implies that $n! + 1 = m^2$ has no solution with $n > 7$, using the search of
Berndt and Galway [BG] up to $10^9$ for the finite part. Since $7/4 < 1.8$, the two results
together give Brocard's conjecture under Baker's explicit abc conjecture.

What this repository adds:

1. **A smaller cutoff.** Row $\varepsilon = 34/71$ of the Laishram-Shorey table gives
   no solution for $n \ge 1039$. The bound $c < N^{7/4}$ used the same way excludes only
   $n \ge 3\,272\,719$ (our computation, `outputs/abc_bound_table.json`, row $\varepsilon = 3/4$).
2. **A certificate** for $8 \le n \le 1038$: 1031 witness primes, checked in the Lean kernel.
3. **A Lean proof** `Brocard.brocard_of_LS` of the full statement from two hypotheses stated as
   propositions.

## Theorem 1 (conditional on explicit abc)

Let $\theta(n) = \sum_{p \le n} \log p$ and write $\omega(x)$ for the number of distinct prime
factors of $x$.

**Hypothesis (H1)** (`LS_abc_34_71` in Lean). For pairwise coprime positive integers $a + b = c$ with
$\omega(abc) \ge 175$,

$$c < \kappa \mathrm{rad}(abc)^{105/71}, \qquad \kappa = \frac{6}{5\sqrt{2\pi \cdot 175}}.$$

This is row $\varepsilon = 34/71$, $\omega_\varepsilon = 175$ of [LS, Theorem 1], which holds under
Baker's explicit abc conjecture. Their theorem requires $\mathrm{rad}(abc) \ge N_\varepsilon$,
the product of the first 175 primes, and $\omega(abc) \ge 175$ implies it.

**Hypothesis (H2)** (`Dusart` in Lean). $\prod_{p \le n} p \le 2.7186^n$ for all $n$. This is a weakening of
$\theta(x) < 1.000081\,x$ [Du; LS, Lemma 2.1(iv)], since $e^{1.000081} < 2.7186$.

**Theorem 1.** Under (H1) and (H2), $n! + 1 = m^2$ implies $n \in \{4, 5, 7\}$.

*Sketch for $n \ge 1039$.* Apply (H1) to the triple $(1, n!, m^2)$. Every prime
$p \le 1039 = p_{175}$ divides $n!$, so $\omega \ge 175$. Since
$\mathrm{rad}(n!\,m^2) \le e^{\theta(n)} m$ and $\kappa \le 1$,

$$m^2 < \bigl(e^{\theta(n)} m\bigr)^{105/71}
\quad\Longrightarrow\quad
(n!)^{37} < m^{74} < e^{210\,\theta(n)}.$$

With $n! \ge (n/e)^n$ and (H2) this needs $(n/e)^{37} < 2.7186^{210}$, which fails once
$n/e \ge 382.2$, that is for every $n \ge 1039$.

The cutoff is set by the prime condition. With Robbins' bound [Ro] and
$\theta(x) < 1.000081\,x$, the size inequality $\log n! < \tfrac{210}{37}\,\theta(n)$ already
fails for every $n \ge 789$, but the hypothesis $\omega(abc) \ge 175$ is only guaranteed from $n = p_{175} = 1039$ on.

## Certificate for $8 \le n \le 1038$

For each $n$ the certificate gives the smallest odd prime $q > n$ such that $n! + 1$ is a
quadratic non-residue modulo $q$:

$$\left(\frac{n! + 1}{q}\right) = -1 \quad\Longrightarrow\quad n! + 1 \ne m^2.$$

The residue $n! \bmod q$ is computed from Wilson's theorem,
$n! \equiv -\bigl((n+1)(n+2)\cdots(q-1)\bigr)^{-1} \pmod q$, and the symbol by Euler's
criterion. The largest gap is $q - n = 88$, at $n = 499$. The file format is in
`certificates/FORMAT.md`. Two independent implementations generate every record, and
`code/verify_certificates.py` checks each record again: primality of $q$ by trial division,
the residue and the minimality of $q$.

In Lean, `Brocard.check_sound` proves that a passing check excludes a square, and the 1031
records are evaluated by `decide +kernel` in 21 chunk files.

## Lean formalization

```lean
theorem Brocard.brocard_of_LS (hLS : LS_abc_34_71) (hD : Dusart) :
    ∀ n m : ℕ, n ! + 1 = m ^ 2 → n = 4 ∨ n = 5 ∨ n = 7
```

| File | Content |
|------|---------|
| `Brocard/Kernel.lean` | $n \le 7$ by hand, parity, $2$-adic and block lemmas, Pell form |
| `Brocard/Witness.lean` | the certificate checker and its soundness proof |
| `Brocard/WitnessData/` | the 1031 witness primes, 50 per file |
| `Brocard/WitnessRange.lean` | `no_solution_8_to_1038` |
| `Brocard/AbcConditional.lean` | the hypotheses, the size argument, `brocard_of_LS` |
| `Brocard/Axioms.lean` | `#print axioms` for the main theorems |

Every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound` (`outputs/lean_axioms.txt`). Toolchain
`leanprover/lean4:v4.33.1`, Mathlib `v4.33.1`.

Mathlib proves only $\prod_{p \le n} p \le 4^n$. With that bound the size argument needs
$n \gtrsim 7100$, so (H2) is kept as a hypothesis to stay at the cutoff 1038.

## A second conditional route (remark)

Zhou [Zh, Theorem A1(i)] states: for coprime $a + b = c$ with $\log|abc| \ge 700$,

$$\log|abc| \le 3 \log \mathrm{rad}(abc) + 8 \sqrt{\log|abc| \cdot \log\log|abc|}.$$

The proof relies on inter-universal Teichmüller theory, whose correctness is disputed [SS],
and the preprint has not been refereed. We record its consequence for Brocard only as a
conditional remark.

For a solution with $n \ge 4$, the triple $\bigl(\tfrac{m-1}{2}, 1, \tfrac{m+1}{2}\bigr)$ is
coprime with $abc = n!/4$ and $\mathrm{rad}(abc) = \mathrm{rad}(n!)$, so $m$ drops
out and $n$ is excluded when

$$L > 3\,\theta(n) + 8\sqrt{L \log L}, \qquad L = \log(n!/4) \ge 700.$$

`code/zhou_route_check.py` checks this in interval arithmetic for $4 \le n \le 10^6$ and proves
the tail by a derivative bound:

* with the exact $\theta(n)$, every $n \ge 480$ is excluded;
* with only $\theta(n) \le n \log 4$ (in Mathlib), every $n \ge 1039$ is excluded.

Together with the certificate, Theorem A1(i) of [Zh] therefore implies Brocard's conjecture,
without (H2). This route is not yet formalized. The two cutoffs at 1039 coincide
by accident: here the bound is set by the term $8\sqrt{L \log L}$, in Theorem 1 by the prime
$p_{175}$.

## Reproducing

```sh
pip install -r requirements.txt
sh reproduce.sh
```

The script regenerates the certificate and compares it byte for byte, verifies it, recomputes
`outputs/` and checks everything against `SHA256SUMS` (about 2 minutes). If `lake` is on the
path it also builds the Lean project and prints the axioms. The Lean build alone:

```sh
cd lean
lake exe cache get
lake build
lake env lean Brocard/Axioms.lean
```

| Path | Content |
|------|---------|
| `certificates/` | the witness file for $1 \le n \le 1038$, its format and hashes |
| `code/witness_certificates.py` | generates the certificate (SymPy and Numba, cross-checked) |
| `code/verify_certificates.py` | verifier: primality, residue, minimality |
| `code/abc_bound_check.py` | all rows of [LS, Theorem 1] in interval arithmetic |
| `code/zhou_route_check.py` | the remark above |
| `lean/` | the Lean project |
| `outputs/` | the computed tables and the axiom list |

## References

* [Ba] A. Baker, *Experiments on the abc-conjecture*, Publ. Math. Debrecen 65 (2004), 253-260.
* [BG] B. C. Berndt and W. F. Galway, *On the Brocard-Ramanujan Diophantine equation
  n! + 1 = m²*, Ramanujan J. 4 (2000), 41-42.
* [Br] J. Browkin, *A weak effective abc-conjecture*, Funct. Approx. Comment. Math. 39 (2008),
  103-111.
* [Du] P. Dusart, *Inégalités explicites pour ψ(X), θ(X), π(X) et les nombres
  premiers*, C. R. Math. Rep. Acad. Sci. Canada 21 (1999), 53-59.
* [LS] S. Laishram and T. N. Shorey, *Baker's explicit abc-conjecture and applications*,
  Acta Arith. 155 (2012), 419-429.
* [Ov] M. Overholt, *The Diophantine equation n! + 1 = m²*, Bull. London Math. Soc. 25
  (1993), 104.
* [Ro] H. Robbins, *A remark on Stirling's formula*, Amer. Math. Monthly 62 (1955), 26-29.
* [SS] P. Scholze and J. Stix, *Why abc is still a conjecture*, manuscript, 2018.
* [Zh] Z.-P. Zhou, *The inter-universal Teichmüller theory and new Diophantine results over the
  rational numbers. I*, arXiv:2503.14510, 2025.

## License

MIT, see `LICENSE`.
