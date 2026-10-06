import Brocard.Radical
import Brocard.Kernel
import Brocard.WitnessRangeZhou
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Brocard's conjecture conditional on Zhou's Theorem A1(i), with natural logarithms. -/

open Nat Finset

namespace Brocard

/-- Zhou, arXiv:2503.14510v1, Theorem A1(i), quoted from p. 2 of the PDF:

“Theorem A1. Let (a, b, c) be a triple of non-zero coprime integers such that a + b = c.
(i) Suppose that log(|abc|) ≥ 700, then we have
log(|abc|) ≤ 3 log rad(abc) + 8 √(log(|abc|) · log log(|abc|)).”

This proposition restricts the statement to positive natural numbers. The logarithm is
the natural logarithm. Coprimality of `a` and `b` and `a + b = c` imply pairwise coprimality. -/
def Zhou_A1i : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (700 : ℝ) ≤ Real.log (a * b * c) →
    Real.log (a * b * c) ≤ 3 * Real.log (rad (a * b * c)) +
      8 * Real.sqrt (Real.log (a * b * c) * Real.log (Real.log (a * b * c)))

/-- Dividing a factorial by four preserves its prime factors for `n ≥ 4`.
The `p = 2` case in `prime_dvd_pair` uses `8 ∣ n!`. -/
theorem rad_pair {n A : ℕ} (hn : 4 ≤ n)
    (hA : 4 * (A * (A + 1)) = n !) : rad (A * (A + 1)) = primorial n := by
  have hpos : 0 < A * (A + 1) := by
    have := Nat.factorial_pos n
    nlinarith
  have hpf : (A * (A + 1)).primeFactors = (n !).primeFactors := by
    ext p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd, _⟩
      refine ⟨hp, ?_, Nat.factorial_ne_zero n⟩
      rw [← hA]
      exact hd.trans (dvd_mul_left _ _)
    · rintro ⟨hp, hd, _⟩
      exact ⟨hp, prime_dvd_pair hn hA hp ((Nat.Prime.dvd_factorial hp).mp hd),
        hpos.ne'⟩
  unfold rad
  rw [hpf]
  exact rad_factorial n

/-- The positive coprime triple `((m-1)/2, 1, (m+1)/2)` for a Brocard solution. -/
theorem zhou_reduction {n m : ℕ} (hn : 4 ≤ n) (h : n ! + 1 = m ^ 2) :
    Odd m ∧ 0 < (m - 1) / 2 ∧
    (m - 1) / 2 + 1 = (m + 1) / 2 ∧ Nat.Coprime ((m - 1) / 2) 1 ∧
    (m - 1) / 2 * 1 * ((m + 1) / 2) = n ! / 4 ∧
    rad ((m - 1) / 2 * 1 * ((m + 1) / 2)) = primorial n := by
  obtain ⟨A, hm, hA, _⟩ := kernel_pair hn h
  have ha : (m - 1) / 2 = A := by omega
  have hc : (m + 1) / 2 = A + 1 := by omega
  have hpos : 0 < A := by
    have := Nat.factorial_pos n
    nlinarith
  rw [ha, hc, mul_one]
  refine ⟨odd_of_eq_sq (by omega) h, hpos, rfl, Nat.coprime_one_right _, ?_,
    rad_pair hn hA⟩
  rw [← hA, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]

/-- `L = log(n!/4)`, with real division. -/
noncomputable def zhouLog (n : ℕ) : ℝ := Real.log ((n ! : ℝ) / 4)

theorem zhouLog_lower {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log n - n - Real.log 4 ≤ zhouLog n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := Real.pow_div_factorial_le_exp (n : ℝ) hnR.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / n !) hb
  rw [Real.log_div (by positivity) hfac.ne', Real.log_pow, Real.log_exp] at hlog
  unfold zhouLog
  rw [Real.log_div hfac.ne' (by norm_num)]
  linarith

theorem zhouLog_upper {n : ℕ} (_hn : 0 < n) :
    zhouLog n ≤ (n : ℝ) * Real.log n := by
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have hpow : (n ! : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hdiv : (n ! : ℝ) / 4 ≤ (n : ℝ) ^ n := by linarith
  simpa [zhouLog, Real.log_pow] using Real.log_le_log (by positivity) hdiv

/-- A calculus-free tail bound; the rational constants leave a margin of `n/20 - 7/5`. -/
theorem zhou_tail_bounds {n : ℕ} (hn : 2048 ≤ n) :
    700 ≤ zhouLog n ∧
    3 * Real.log (primorial n) +
      8 * Real.sqrt (zhouLog n * Real.log (zhouLog n)) < zhouLog n := by
  have hnR : (2048 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by positivity
  have hlogn : (7 : ℝ) ≤ Real.log n := by
    have hb := Real.log_le_log (by norm_num : (0 : ℝ) < 2048) hnR
    have heq : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
      rw [show (2048 : ℝ) = 2 ^ 11 by norm_num, Real.log_pow]
      norm_num
    rw [heq] at hb
    linarith [Real.log_two_gt_d9]
  have hlog4 : Real.log 4 ≤ (7 : ℝ) / 5 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hlo := zhouLog_lower hnpos
  have hhi := zhouLog_upper hnpos
  have hL700 : 700 ≤ zhouLog n := by
    have := mul_le_mul_of_nonneg_left hlogn hn0.le
    linarith
  have hL0 : 0 < zhouLog n := by linarith
  have hlogL : Real.log (zhouLog n) ≤ 2 * Real.log n := by
    have hln : Real.log (n : ℝ) ≤ n := by
      linarith [Real.log_le_sub_one_of_pos hn0]
    have hLsq : zhouLog n ≤ (n : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hln hn0.le]
    have hb := Real.log_le_log hL0 hLsq
    simpa [Real.log_pow] using hb
  have hprod : zhouLog n * Real.log (zhouLog n) ≤
      2 * (n : ℝ) * (Real.log n) ^ 2 := by
    have hlogL0 : 0 ≤ Real.log (zhouLog n) := Real.log_nonneg (by linarith)
    calc zhouLog n * Real.log (zhouLog n)
        ≤ ((n : ℝ) * Real.log n) * (2 * Real.log n) :=
          mul_le_mul hhi hlogL hlogL0 (by positivity)
      _ = _ := by ring
  have hroot : Real.sqrt (zhouLog n * Real.log (zhouLog n)) ≤
      (n : ℝ) * Real.log n / 32 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hcoef : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 / 1024 := by nlinarith
    have hb := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (Real.log n))
    nlinarith
  have hprim : Real.log (primorial n) ≤ (n : ℝ) * Real.log 4 := by
    have hP : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
    have hbound : (primorial n : ℝ) ≤ (4 : ℝ) ^ n := by
      exact_mod_cast primorial_le_four_pow n
    simpa [Real.log_pow] using Real.log_le_log hP hbound
  refine ⟨hL700, ?_⟩
  have hmargin : 3 * (n : ℝ) * Real.log 4 + (n : ℝ) * Real.log n / 4 <
      (n : ℝ) * Real.log n - n - Real.log 4 := by
    have hb4 := mul_le_mul_of_nonneg_left hlog4 hn0.le
    have hbn := mul_le_mul_of_nonneg_left hlogn hn0.le
    nlinarith
  linarith

/-- Zhou's inequality contradicts the factorial bounds for every `n ≥ 2048`. -/
theorem no_solution_of_Zhou (hZ : Zhou_A1i) {n m : ℕ} (hn : 2048 ≤ n)
    (h : n ! + 1 = m ^ 2) : False := by
  obtain ⟨_, ha, hac, hcop, hprod, hrad⟩ := zhou_reduction (by omega) h
  have hd4 : 4 ∣ n ! := (by decide : 4 ∣ 4 !).trans
    (Nat.factorial_dvd_factorial (by omega : 4 ≤ n))
  have hcast : (((m - 1) / 2 : ℕ) : ℝ) * 1 * (((m + 1) / 2 : ℕ) : ℝ) =
      (n ! : ℝ) / 4 := by
    have hb := congrArg (fun k : ℕ => (k : ℝ)) hprod
    rw [Nat.cast_div hd4 (by norm_num)] at hb
    norm_num at hb
    simpa using hb
  have hlog : Real.log ((((m - 1) / 2 : ℕ) : ℝ) * 1 *
      (((m + 1) / 2 : ℕ) : ℝ)) = zhouLog n := by rw [hcast]; rfl
  obtain ⟨h700, hstrict⟩ := zhou_tail_bounds hn
  have hZ' := hZ ((m - 1) / 2) 1 ((m + 1) / 2) ha one_pos hcop hac
    (by simpa only [Nat.cast_one, hlog] using h700)
  rw [Nat.cast_one, hlog, hrad] at hZ'
  linarith

/-- Zhou A1(i) alone implies Brocard's conjecture. -/
theorem brocard_of_Zhou (hZ : Zhou_A1i) :
    ∀ n m : ℕ, n ! + 1 = m ^ 2 → n = 4 ∨ n = 5 ∨ n = 7 := by
  intro n m h
  by_cases h7 : n ≤ 7
  · exact (solutions_le_seven h7).mp ⟨m, h⟩
  · by_cases h2047 : n ≤ 2047
    · exact absurd ⟨m, h⟩ (no_solution_8_to_2047 n (by omega) h2047)
    · exact (no_solution_of_Zhou hZ (by omega) h).elim

end Brocard
