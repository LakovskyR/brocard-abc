import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Brocard kernel (elementary part)

Elementary only: no abc, no Baker, no Størmer. No `sorry`. Axioms are listed in
outputs/lean_axioms.txt via `#print axioms` (Brocard/Axioms.lean).

Equation: `n ! + 1 = m ^ 2` in natural numbers.
-/

open Nat

namespace Brocard

/-! ## §1. Parity of m -/

/-- For `n ≥ 2`, `n! + 1 = m^2` forces `m` odd. -/
theorem odd_of_eq_sq {n m : ℕ} (hn : 2 ≤ n) (h : n ! + 1 = m ^ 2) : Odd m := by
  have h2 : 2 ∣ n ! := Nat.dvd_factorial (by norm_num) hn
  have hodd : Odd (m ^ 2) := by
    rw [← h]
    exact (even_iff_two_dvd.mpr h2).add_one
  exact (Nat.odd_pow_iff (by norm_num)).mp hodd

/-! ## §2. The pair A = (m-1)/2, B = A + 1 -/

/-- For `n ≥ 4`: `m = 2A + 1`, `4·A(A+1) = n!`, and `A`, `A+1` are coprime. -/
theorem kernel_pair {n m : ℕ} (hn : 4 ≤ n) (h : n ! + 1 = m ^ 2) :
    ∃ A : ℕ, m = 2 * A + 1 ∧ 4 * (A * (A + 1)) = n ! ∧ Nat.Coprime A (A + 1) := by
  obtain ⟨A, rfl⟩ := odd_of_eq_sq (by omega) h
  refine ⟨A, rfl, ?_, ?_⟩
  · have : (2 * A + 1) ^ 2 = 4 * (A * (A + 1)) + 1 := by ring
    omega
  · exact (Nat.coprime_self_add_right (m := A) (n := 1)).mpr (Nat.coprime_one_right A)

/-! ## §3. Block lemma -/

/-- Every prime `p ≤ n` divides `A(A+1)` when `4·A(A+1) = n!` and `n ≥ 4`
(the `p = 2` case uses `8 ∣ n!`). -/
theorem prime_dvd_pair {n A : ℕ} (hn : 4 ≤ n) (hA : 4 * (A * (A + 1)) = n !)
    {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ A * (A + 1) := by
  rcases hp.eq_two_or_odd with rfl | hodd
  · have h8 : 8 ∣ n ! := (by decide : 8 ∣ 4 !).trans (Nat.factorial_dvd_factorial hn)
    rw [← hA] at h8
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp (by simpa using h8)
  · have hpf : p ∣ n ! := (Nat.Prime.dvd_factorial hp).mpr hpn
    rw [← hA] at hpf
    have hc : Nat.Coprime p 4 := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h4
      have h4' : p ∣ 2 ^ 2 := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h4'
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
      omega
    exact hc.dvd_of_dvd_mul_left hpf

/-- Block lemma. For every prime `p ≤ n`, with
`e = v_p(A(A+1)) = v_p(n!/4)`: `e ≥ 1`, and exactly one of `A`, `A+1` is divisible by `p`;
that one carries the whole block (`v_p = e`) and the other has `v_p = 0`. -/
theorem block_lemma {n A : ℕ} (hn : 4 ≤ n) (hA : 4 * (A * (A + 1)) = n !)
    {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    1 ≤ padicValNat p (A * (A + 1)) ∧
    ((padicValNat p A = padicValNat p (A * (A + 1)) ∧ ¬ p ∣ A + 1) ∨
     (padicValNat p (A + 1) = padicValNat p (A * (A + 1)) ∧ ¬ p ∣ A)) := by
  have := Fact.mk hp
  have hX0 : A * (A + 1) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hA; exact (Nat.factorial_pos n).ne' hA.symm
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hX0
  have hprod := prime_dvd_pair hn hA hp hpn
  refine ⟨one_le_padicValNat_of_dvd hX0 hprod, ?_⟩
  rw [padicValNat.mul hA0 (Nat.succ_ne_zero A)]
  rcases hp.dvd_mul.mp hprod with hdA | hdB
  · have hnB : ¬ p ∣ A + 1 := fun hdB =>
      hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdA).mp hdB))
    left
    exact ⟨by rw [padicValNat.eq_zero_of_not_dvd hnB, add_zero], hnB⟩
  · have hnA : ¬ p ∣ A := fun hdA =>
      hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdA).mp hdB))
    right
    exact ⟨by rw [padicValNat.eq_zero_of_not_dvd hnA, zero_add], hnA⟩

/-- Divisibility form of the block lemma: the full block `p^e` divides exactly one of `A`, `A+1`. -/
theorem block_dvd {n A : ℕ} (hn : 4 ≤ n) (hA : 4 * (A * (A + 1)) = n !)
    {p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    (p ^ padicValNat p (A * (A + 1)) ∣ A ∧ ¬ p ^ padicValNat p (A * (A + 1)) ∣ A + 1) ∨
    (p ^ padicValNat p (A * (A + 1)) ∣ A + 1 ∧ ¬ p ^ padicValNat p (A * (A + 1)) ∣ A) := by
  have := Fact.mk hp
  obtain ⟨he, hcase⟩ := block_lemma hn hA hp hpn
  have hpe : p ∣ p ^ padicValNat p (A * (A + 1)) := dvd_pow_self p (by omega)
  rcases hcase with ⟨hv, hnB⟩ | ⟨hv, hnA⟩
  · left
    exact ⟨hv ▸ pow_padicValNat_dvd, fun h => hnB (hpe.trans h)⟩
  · right
    exact ⟨hv ▸ pow_padicValNat_dvd, fun h => hnA (hpe.trans h)⟩

/-- 2-adic case: `v_2(A(A+1)) = v_2(n!) - 2 = n - s_2(n) - 2` (Legendre in base 2). -/
theorem two_adic {n A : ℕ} (hA : 4 * (A * (A + 1)) = n !) :
    padicValNat 2 (A * (A + 1)) + 2 = n - (Nat.digits 2 n).sum := by
  have := Fact.mk Nat.prime_two
  have hX0 : A * (A + 1) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hA; exact (Nat.factorial_pos n).ne' hA.symm
  have hL := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [← hA, padicValNat.mul (by norm_num) hX0,
    show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow] at hL
  omega

/-- Exactly one of `A`, `A+1` is even; the whole 2-block sits in that one (block lemma at p = 2). -/
theorem even_side (A : ℕ) : Even A ↔ ¬ Even (A + 1) := by
  rw [Nat.even_add_one]; tauto

/-! ## §4. Edge cases -/

/-- No solution for `n < 4` (`n! + 1 = 2, 2, 3, 7`). -/
theorem no_solution_lt_four {n m : ℕ} (hn : n < 4) (h : n ! + 1 = m ^ 2) : False := by
  interval_cases n <;> norm_num [Nat.factorial] at h <;>
    (have hm : m ≤ 3 := by nlinarith) <;> interval_cases m <;> omega

/-- No solution at `n = 6` (`721` is not a square). -/
theorem no_solution_six {m : ℕ} (h : 6 ! + 1 = m ^ 2) : False := by
  norm_num [Nat.factorial] at h
  have hm : m ≤ 27 := by nlinarith
  interval_cases m <;> omega

/-- For `n ≤ 7` the solutions are exactly `n ∈ {4, 5, 7}` (`m = 5, 11, 71`). -/
theorem solutions_le_seven {n : ℕ} (hn : n ≤ 7) :
    (∃ m, n ! + 1 = m ^ 2) ↔ n = 4 ∨ n = 5 ∨ n = 7 := by
  constructor
  · rintro ⟨m, h⟩
    interval_cases n <;> norm_num [Nat.factorial] at h ⊢ <;>
      (have hm : m ≤ 27 := by nlinarith) <;> interval_cases m <;> omega
  · rintro (rfl | rfl | rfl)
    · exact ⟨5, by decide⟩
    · exact ⟨11, by decide⟩
    · exact ⟨71, by decide⟩

/-! ## §5. Pell form -/

/-- Squarefree kernel of `n!`: the product of the primes with odd exponent in `n!`. -/
def D (n : ℕ) : ℕ := (n !).factorization.prod fun p e => p ^ (e % 2)

/-- `Y n = sqrt(n! / D n)`, as an exact product. -/
def Y (n : ℕ) : ℕ := (n !).factorization.prod fun p e => p ^ (e / 2)

theorem factorial_eq_D_mul_Y_sq (n : ℕ) : n ! = D n * Y n ^ 2 := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero n)]
  unfold D Y
  simp only [Finsupp.prod]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul, ← pow_add, Nat.mod_add_div']

/-- Pell equivalence: `n! + 1 = m^2 ↔ m^2 = D_n Y_n^2 + 1`. -/
theorem pell_iff (n m : ℕ) : n ! + 1 = m ^ 2 ↔ m ^ 2 = D n * Y n ^ 2 + 1 := by
  rw [factorial_eq_D_mul_Y_sq n]; exact eq_comm

/-- Same, written as the Pell equation `X^2 - D Y^2 = 1` over the integers. -/
theorem pell_iff_int (n m : ℕ) :
    n ! + 1 = m ^ 2 ↔ (m : ℤ) ^ 2 - (D n : ℤ) * (Y n : ℤ) ^ 2 = 1 := by
  rw [pell_iff]
  constructor
  · intro h
    have h' : ((m ^ 2 : ℕ) : ℤ) = ((D n * Y n ^ 2 + 1 : ℕ) : ℤ) := by rw [h]
    push_cast at h'
    linarith
  · intro h
    have h' : ((m ^ 2 : ℕ) : ℤ) = ((D n * Y n ^ 2 + 1 : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h'

theorem D_ne_zero (n : ℕ) : D n ≠ 0 := by
  intro h0
  have := factorial_eq_D_mul_Y_sq n
  rw [h0, zero_mul] at this
  exact Nat.factorial_ne_zero n this

/-- `D n` is squarefree. -/
theorem squarefree_D (n : ℕ) : Squarefree (D n) := by
  have hD : D n = (Finsupp.mapRange (· % 2) (by simp) (n !).factorization).prod (· ^ ·) := by
    unfold D
    rw [Finsupp.prod_mapRange_index]
    intro a; simp
  rw [Nat.squarefree_iff_factorization_le_one (D_ne_zero n), hD,
    Nat.prod_pow_factorization_eq_self]
  · intro p
    simp only [Finsupp.mapRange_apply]
    omega
  · intro p hp
    have hp' := Finsupp.support_mapRange hp
    rw [Nat.support_factorization] at hp'
    exact Nat.prime_of_mem_primeFactors hp'

end Brocard
