import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

/-!
# Brocard witness checker

A verified checker for the certificate format in certificates/FORMAT.md.

`check n q` computes `r = (n! + 1) mod q` by a structural fold and tests Euler's criterion
`r^((q-1)/2) ≡ -1 (mod q)` for an odd prime `q > n`. `check_sound` proves that a passing
check excludes `n! + 1 = m^2`. `no_solution_8_to_1038` runs the checker on the witness primes
of certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc).

The 1031 records are checked in 21 chunk files (Brocard/WitnessData/), see `chunk_sound`.
No `sorry`.
-/

open Nat

namespace Brocard

/-- `n! mod q` by structural recursion (kernel-reducible, no big intermediate values). -/
def factMod : ℕ → ℕ → ℕ
  | 0, q => 1 % q
  | n + 1, q => (factMod n q * (n + 1)) % q

theorem factMod_eq (n q : ℕ) : factMod n q = n ! % q := by
  induction n with
  | zero => simp [factMod]
  | succ n ih =>
    rw [factMod, ih, Nat.factorial_succ, mul_comm (n + 1), Nat.mod_mul_mod]

/-- Euler-criterion witness test: `q` odd, `r = (n! + 1) mod q ≠ 0`, `r^((q-1)/2) ≡ q - 1`. -/
def check (n q : ℕ) : Bool :=
  let r := (factMod n q + 1) % q
  q % 2 == 1 && r != 0 && (r ^ ((q - 1) / 2)) % q == q - 1

/-- Trial-division primality test, kernel-reducible. -/
def isPrimeTD (q : ℕ) : Bool :=
  2 ≤ q && (List.range q).all fun d => d < 2 || q % d != 0

theorem prime_of_isPrimeTD {q : ℕ} (h : isPrimeTD q = true) : q.Prime := by
  unfold isPrimeTD at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h2, hd⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨h2, fun d hd2 hdq hdvd => ?_⟩
  rcases hd d hdq with h | h
  · omega
  · exact h (Nat.mod_eq_zero_of_dvd hdvd)

/-- Soundness of the witness test: a passing check for a prime `q > n` excludes a square. -/
theorem check_sound {n q : ℕ} (hq : q.Prime) (_hnq : n < q) (h : check n q = true) :
    ¬ ∃ m, n ! + 1 = m ^ 2 := by
  rintro ⟨m, hm⟩
  have := Fact.mk hq
  unfold check at h
  simp only [factMod_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hq2, hr0⟩, hpow⟩ := h
  have hr : (n ! % q + 1) % q = (n ! + 1) % q := Nat.mod_add_mod _ _ _
  rw [hr] at hr0 hpow
  have hcast : (((n ! + 1) % q : ℕ) : ZMod q) = ((n ! + 1 : ℕ) : ZMod q) := ZMod.natCast_mod _ _
  have hsq : IsSquare (((n ! + 1) % q : ℕ) : ZMod q) := by
    rw [hcast, hm]; push_cast; exact ⟨(m : ZMod q), by ring⟩
  have hne : (((n ! + 1) % q : ℕ) : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hr0 (Nat.eq_zero_of_dvd_of_lt hdvd (Nat.mod_lt _ hq.pos))
  have heuler := (ZMod.euler_criterion q hne).mp hsq
  have hexp : q / 2 = (q - 1) / 2 := by omega
  have hneg : (((n ! + 1) % q : ℕ) : ZMod q) ^ ((q - 1) / 2) = -1 := by
    have h1 : (((((n ! + 1) % q) ^ ((q - 1) / 2)) % q : ℕ) : ZMod q) = ((q - 1 : ℕ) : ZMod q) := by
      rw [hpow]
    rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_sub hq.one_le, ZMod.natCast_self, Nat.cast_one,
      zero_sub] at h1
    exact h1
  rw [hexp, hneg] at heuler
  have : Fact (2 < q) := ⟨by have := hq.two_le; omega⟩
  exact ZMod.neg_one_ne_one heuler

/-- Full per-record check: `q` prime by trial division, `n < q`, and the Euler witness test. -/
def recordOk (n q : ℕ) : Bool := isPrimeTD q && decide (n < q) && check n q

theorem recordOk_sound {n q : ℕ} (h : recordOk n q = true) : ¬ ∃ m, n ! + 1 = m ^ 2 := by
  unfold recordOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact check_sound (prime_of_isPrimeTD h.1.1) h.1.2 h.2

/-- A verified chunk `∀ j < len, recordOk (j + lo) (w[j]) = true` excludes every `n` in
`[lo, lo + len)`. The chunks live in `Brocard/WitnessData/ChunkNN.lean`, 50 records each,
proved by `decide +kernel` (kernel evaluation, no extra axiom); `Brocard/WitnessRange.lean`
glues them into `no_solution_8_to_1038`. -/
theorem chunk_sound {lo len : ℕ} {w : List ℕ}
    (h : ∀ j < len, recordOk (j + lo) (w.getD j 0) = true) :
    ∀ n, lo ≤ n → n < lo + len → ¬ ∃ m, n ! + 1 = m ^ 2 := by
  intro n h1 h2
  have := h (n - lo) (by omega)
  rw [Nat.sub_add_cancel h1] at this
  exact recordOk_sound this

theorem range_glue {P : ℕ → Prop} {a b c : ℕ}
    (h1 : ∀ n, a ≤ n → n < b → P n) (h2 : ∀ n, b ≤ n → n < c → P n) :
    ∀ n, a ≤ n → n < c → P n := by
  intro n ha hc
  by_cases hb : n < b
  · exact h1 n ha hb
  · exact h2 n (by omega) hc

end Brocard
