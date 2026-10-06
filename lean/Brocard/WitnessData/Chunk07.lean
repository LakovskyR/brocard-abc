import Brocard.Witness

/-! Witness records n = 358..407 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w07 : List ℕ := [
  379, 367, 373, 379, 367, 367, 373, 373, 373, 383, 389, 373,
  373, 373, 379, 397, 389, 379, 379, 379, 389, 401, 389, 397,
  397, 401, 389, 419, 389, 389, 431, 409, 397, 401, 397, 409,
  397, 397, 409, 401, 419, 409, 419, 409, 409, 421, 421, 409,
  421, 419]

theorem chunk07 : ∀ j < 50, Brocard.recordOk (j + 358) (w07.getD j 0) = true := by
  decide +kernel

theorem chunk07_sound : ∀ n, 358 ≤ n → n < 408 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk07

end Brocard.WitnessData
