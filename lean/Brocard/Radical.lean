import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Prime.Factorial

/-! The radical and its value on a factorial, shared by the conditional proofs. -/

open Nat Finset

namespace Brocard

/-- Radical: the product of the distinct prime factors. -/
def rad (x : ℕ) : ℕ := ∏ p ∈ x.primeFactors, p

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

end Brocard
