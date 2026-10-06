import Brocard.Witness

/-! Witness records n = 8..57 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w00 : List ℕ := [
  11, 11, 13, 13, 29, 23, 31, 37, 19, 19, 31, 23,
  29, 31, 37, 59, 31, 31, 29, 29, 43, 37, 37, 41,
  41, 37, 37, 37, 41, 43, 53, 43, 43, 43, 47, 61,
  53, 53, 71, 53, 53, 67, 53, 53, 59, 59, 67, 59,
  59, 59]

theorem chunk00 : ∀ j < 50, Brocard.recordOk (j + 8) (w00.getD j 0) = true := by
  decide +kernel

theorem chunk00_sound : ∀ n, 8 ≤ n → n < 58 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk00

end Brocard.WitnessData
