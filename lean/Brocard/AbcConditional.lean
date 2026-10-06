import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic
import Brocard.Kernel
import Brocard.WitnessRange

/-!
# Brocard, conditional part: explicit abc ⇒ Brocard

The size argument for `n ≥ 1039`, row ε = 34/71 of Laishram-Shorey 2012, Theorem 1.

Two hypotheses are stated as `Prop`s and assumed, never proved here:

* `LS_abc_34_71`: the consequence of Laishram-Shorey 2012, Theorem 1 (row ε = 34/71,
  ω_ε = 175, exponent 1 + ε = 105/71, κ = 6/(5·sqrt(2π·175))), which holds under Baker's
  explicit abc conjecture (their Conjecture 1.2). We assume the consequence, not the
  conjecture, so their Theorem 1 is not formalized.
* `Dusart`: `primorial n ≤ 2.7186^n`, a weakening of Dusart 1999, θ(x) < 1.000081·x
  (Laishram-Shorey Lemma 2.1(iv); exp(1.000081) = 2.71850… < 2.7186). Mathlib only has
  `primorial n ≤ 4^n`; with that bound alone the size threshold moves to n ≈ 7100 and the
  certificate range would have to be extended. Choice made here: keep
  N_0 = 1038 and state Dusart as a hypothesis.

Main result: `brocard_of_LS : LS_abc_34_71 → Dusart → ∀ n m, n ! + 1 = m ^ 2 → n ∈ {4, 5, 7}`.
Ingredients: Kernel.lean (n ≤ 7), WitnessRange.lean (8 ≤ n ≤ 1038), and the size argument here
(n ≥ 1039). No `sorry`.
-/

open Nat Finset

namespace Brocard

/-- Radical: the product of the distinct prime factors. -/
def rad (x : ℕ) : ℕ := ∏ p ∈ x.primeFactors, p

/-- Laishram-Shorey 2012, Theorem 1, row ε = 34/71, as a consequence of Baker's explicit abc:
for pairwise coprime positive `a + b = c` with `ω(abc) ≥ 175`,
`c < κ · rad(abc)^(105/71)` with `κ = 6/(5·sqrt(2π·175))`. -/
def LS_abc_34_71 : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
    a + b = c → 175 ≤ (a * b * c).primeFactors.card →
    (c : ℝ) < 6 / (5 * Real.sqrt (2 * Real.pi * 175)) *
      (rad (a * b * c) : ℝ) ^ ((105 : ℝ) / 71)

/-- Dusart 1999 (weakened): `primorial n ≤ 2.7186^n`. -/
def Dusart : Prop := ∀ n : ℕ, (primorial n : ℝ) ≤ (2.7186 : ℝ) ^ n

theorem kappa_le_one : 6 / (5 * Real.sqrt (2 * Real.pi * 175)) ≤ 1 := by
  have hpi := Real.pi_gt_three
  have hs : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi * 175) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [div_le_one (by positivity)]
  linarith

/-- Converse of `prime_of_isPrimeTD`: the trial-division checker accepts every prime. -/
theorem isPrimeTD_of_prime {q : ℕ} (hq : q.Prime) : isPrimeTD q = true := by
  unfold isPrimeTD
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hq.two_le, fun d hd => ?_⟩
  by_cases h2 : d < 2
  · exact Or.inl h2
  · right
    intro hmod
    exact (Nat.prime_def_lt'.mp hq).2 d (by omega) hd (Nat.dvd_of_mod_eq_zero hmod)

/-- `π(1039) = 175` (there are 175 primes below 1040; `p_175 = 1039`). Decided in the kernel
through the Bool checker `isPrimeTD` (Mathlib's `Nat.decidablePrime` takes 20 minutes here). -/
theorem card_primes_lt_1040 : ((Finset.range 1040).filter Nat.Prime).card = 175 := by
  rw [Finset.filter_congr (q := fun p => isPrimeTD p = true)
    (fun p _ => ⟨isPrimeTD_of_prime, prime_of_isPrimeTD⟩)]
  decide +kernel

theorem primeFactors_factorial (n : ℕ) :
    (n !).primeFactors = (Finset.range (n + 1)).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hd, -⟩
    exact ⟨by have := (Nat.Prime.dvd_factorial hp).mp hd; omega, hp⟩
  · rintro ⟨hlt, hp⟩
    exact ⟨hp, (Nat.Prime.dvd_factorial hp).mpr (by omega), Nat.factorial_ne_zero n⟩

theorem rad_factorial (n : ℕ) : rad (n !) = primorial n := by
  unfold rad primorial
  rw [primeFactors_factorial]

/-- `ω(n! · m²) ≥ 175` for `n ≥ 1039`. -/
theorem omega_ge {n m : ℕ} (hn : 1039 ≤ n) (hm : m ≠ 0) :
    175 ≤ (n ! * m ^ 2).primeFactors.card := by
  rw [← card_primes_lt_1040]
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  have h1 : p ∈ (n !).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hp.2, (Nat.Prime.dvd_factorial hp.2).mpr (by omega), Nat.factorial_ne_zero n⟩
  exact Nat.primeFactors_mono (Dvd.intro _ rfl)
    (mul_ne_zero (Nat.factorial_ne_zero n) (pow_ne_zero 2 hm)) h1

/-- `rad(n! · m²) ≤ primorial n · m`. -/
theorem rad_le {n m : ℕ} (hm : 0 < m) (_hcop : Nat.Coprime (n !) m) :
    rad (n ! * m ^ 2) ≤ primorial n * m := by
  unfold rad
  rw [Nat.primeFactors_mul (Nat.factorial_ne_zero n) (pow_ne_zero 2 hm.ne'),
    Nat.primeFactors_pow m two_ne_zero]
  calc ∏ p ∈ (n !).primeFactors ∪ m.primeFactors, p
      ≤ (∏ p ∈ (n !).primeFactors, p) * ∏ p ∈ m.primeFactors, p := by
        rw [← Finset.prod_union_inter]
        exact Nat.le_mul_of_pos_right _ (Finset.prod_pos fun p hp =>
          (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1).pos)
    _ ≤ primorial n * m := by
        rw [← rad_factorial]
        unfold rad
        exact Nat.mul_le_mul le_rfl (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m))

/-- The size argument for `n ≥ 1039`, from the LS inequality specialised to `(1, n!, m²)`. -/
theorem size_contradiction (hD : Dusart) {n m : ℕ} (hn : 1039 ≤ n) (h : n ! + 1 = m ^ 2)
    (hLS : (m : ℝ) ^ 2 < 6 / (5 * Real.sqrt (2 * Real.pi * 175)) *
      (rad (n ! * m ^ 2) : ℝ) ^ ((105 : ℝ) / 71)) : False := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · simp at h
    · exact h'
  have hcop2 : Nat.Coprime (n !) (m ^ 2) := by
    rw [← h]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hcop : Nat.Coprime (n !) m := hcop2.coprime_dvd_right (dvd_pow_self m two_ne_zero)
  have hrad : (rad (n ! * m ^ 2) : ℝ) ≤ (primorial n : ℝ) * m := by
    exact_mod_cast rad_le hm0 hcop
  have hM : (0 : ℝ) < m := by exact_mod_cast hm0
  have hP0 : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have hrad0 : (0 : ℝ) ≤ rad (n ! * m ^ 2) := by positivity
  -- step 1: m^2 < (P m)^(105/71)
  have h1 : (m : ℝ) ^ 2 < ((primorial n : ℝ) * m) ^ ((105 : ℝ) / 71) := by
    calc (m : ℝ) ^ 2 < _ := hLS
      _ ≤ 1 * (rad (n ! * m ^ 2) : ℝ) ^ ((105 : ℝ) / 71) :=
        mul_le_mul_of_nonneg_right kappa_le_one (by positivity)
      _ = (rad (n ! * m ^ 2) : ℝ) ^ ((105 : ℝ) / 71) := one_mul _
      _ ≤ ((primorial n : ℝ) * m) ^ ((105 : ℝ) / 71) :=
        Real.rpow_le_rpow hrad0 hrad (by norm_num)
  -- step 2: m^142 < (P m)^105
  have h2 : (m : ℝ) ^ 142 < ((primorial n : ℝ) * m) ^ 105 := by
    have h71 := pow_lt_pow_left₀ h1 (by positivity) (by norm_num : (71 : ℕ) ≠ 0)
    rw [← pow_mul, ← Real.rpow_natCast (((primorial n : ℝ) * m) ^ ((105 : ℝ) / 71)) 71,
      ← Real.rpow_mul (by positivity)] at h71
    norm_num at h71
    exact h71
  -- step 3: m^37 < P^105
  have h3 : (m : ℝ) ^ 37 < (primorial n : ℝ) ^ 105 := by
    have h' : (m : ℝ) ^ 37 * (m : ℝ) ^ 105 < (primorial n : ℝ) ^ 105 * (m : ℝ) ^ 105 := by
      rw [← pow_add, ← mul_pow]; exact h2
    exact lt_of_mul_lt_mul_right h' (by positivity)
  -- step 4: (n!)^37 < P^210
  have hN : (n ! : ℝ) < (m : ℝ) ^ 2 := by
    have : n ! < m ^ 2 := by rw [← h]; exact Nat.lt_succ_self _
    exact_mod_cast this
  have h4 : (n ! : ℝ) ^ 37 < (primorial n : ℝ) ^ 210 := by
    calc (n ! : ℝ) ^ 37 < ((m : ℝ) ^ 2) ^ 37 :=
          pow_lt_pow_left₀ hN (by positivity) (by norm_num)
      _ = ((m : ℝ) ^ 37) ^ 2 := by ring
      _ < ((primorial n : ℝ) ^ 105) ^ 2 := pow_lt_pow_left₀ h3 (by positivity) (by norm_num)
      _ = (primorial n : ℝ) ^ 210 := by ring
  -- step 5: Dusart: P^210 ≤ (2.7186^210)^n
  have h5 : (primorial n : ℝ) ^ 210 ≤ ((2.7186 : ℝ) ^ 210) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ hP0.le (hD n) 210
  -- step 6: n! ≥ (n / 2.7182818286)^n
  have hfac : ((n : ℝ) / 2.7182818286) ^ n ≤ (n ! : ℝ) := by
    have h6 := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
    have hen : Real.exp (n : ℝ) ≤ (2.7182818286 : ℝ) ^ n := by
      rw [← Real.exp_one_rpow, Real.rpow_natCast]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
    rw [div_le_iff₀ (by positivity)] at h6
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc (n : ℝ) ^ n ≤ Real.exp n * (n ! : ℝ) := h6
      _ ≤ (2.7182818286 : ℝ) ^ n * (n ! : ℝ) := by gcongr
      _ = (n ! : ℝ) * (2.7182818286 : ℝ) ^ n := mul_comm _ _
  -- step 7: 2.7186^210 ≤ (n / 2.7182818286)^37 for n ≥ 1039
  have h7 : (2.7186 : ℝ) ^ 210 ≤ ((n : ℝ) / 2.7182818286) ^ 37 := by
    have hn' : (382.2 : ℝ) ≤ (n : ℝ) / 2.7182818286 := by
      rw [le_div_iff₀ (by norm_num)]
      have : (1039 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    calc (2.7186 : ℝ) ^ 210 ≤ (382.2 : ℝ) ^ 37 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hn' 37
  -- combine
  have h8 : ((2.7186 : ℝ) ^ 210) ^ n ≤ (n ! : ℝ) ^ 37 := by
    calc ((2.7186 : ℝ) ^ 210) ^ n ≤ (((n : ℝ) / 2.7182818286) ^ 37) ^ n :=
          pow_le_pow_left₀ (by positivity) h7 n
      _ = (((n : ℝ) / 2.7182818286) ^ n) ^ 37 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (n ! : ℝ) ^ 37 := pow_le_pow_left₀ (by positivity) hfac 37
  linarith [h4, h5, h8]

/-- abc half: under `LS_abc_34_71` and `Dusart`, no solution with `n ≥ 1039`. -/
theorem no_solution_of_LS (hLS : LS_abc_34_71) (hD : Dusart) {n m : ℕ} (hn : 1039 ≤ n)
    (h : n ! + 1 = m ^ 2) : False := by
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · simp at h
    · exact h'
  have hcop2 : Nat.Coprime (n !) (m ^ 2) := by
    rw [← h]; exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hLS' := hLS 1 (n !) (m ^ 2) one_pos (Nat.factorial_pos n) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) hcop2 (by rw [add_comm]; exact h)
    (by rw [one_mul]; exact omega_ge hn hm0.ne')
  rw [one_mul] at hLS'
  push_cast at hLS'
  exact size_contradiction hD hn h hLS'

/-- Main theorem: explicit abc (Laishram-Shorey row 34/71) + Dusart ⇒ Brocard. -/
theorem brocard_of_LS (hLS : LS_abc_34_71) (hD : Dusart) :
    ∀ n m : ℕ, n ! + 1 = m ^ 2 → n = 4 ∨ n = 5 ∨ n = 7 := by
  intro n m h
  by_cases h7 : n ≤ 7
  · exact (solutions_le_seven h7).mp ⟨m, h⟩
  · by_cases h1038 : n ≤ 1038
    · exact absurd ⟨m, h⟩ (no_solution_8_to_1038 n (by omega) h1038)
    · exact (no_solution_of_LS hLS hD (by omega) h).elim

/-- Same statement with a set membership, the shape used by formal-conjectures. -/
theorem brocard_of_LS' (hLS : LS_abc_34_71) (hD : Dusart) :
    ∀ n m : ℕ, n ! + 1 = m ^ 2 → n ∈ ({4, 5, 7} : Set ℕ) := by
  intro n m h
  have := brocard_of_LS hLS hD n m h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact this

end Brocard
