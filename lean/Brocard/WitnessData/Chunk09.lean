import Brocard.Witness

/-! Witness records n = 458..507 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w09 : List ℕ := [
  461, 461, 467, 479, 467, 467, 467, 467, 499, 499, 479, 487,
  479, 491, 487, 491, 491, 487, 487, 491, 487, 491, 487, 491,
  491, 491, 491, 491, 499, 503, 491, 491, 499, 499, 499, 509,
  499, 499, 499, 499, 509, 587, 509, 509, 509, 521, 523, 509,
  509, 509]

theorem chunk09 : ∀ j < 50, Brocard.recordOk (j + 458) (w09.getD j 0) = true := by
  decide +kernel

theorem chunk09_sound : ∀ n, 458 ≤ n → n < 508 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk09

end Brocard.WitnessData
