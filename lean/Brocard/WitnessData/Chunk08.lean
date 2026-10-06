import Brocard.Witness

/-! Witness records n = 408..457 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w08 : List ℕ := [
  421, 419, 421, 421, 421, 419, 419, 419, 419, 419, 421, 421,
  443, 431, 431, 431, 439, 439, 433, 431, 433, 433, 439, 449,
  443, 439, 461, 439, 461, 461, 449, 457, 443, 443, 449, 449,
  449, 449, 479, 463, 463, 457, 457, 457, 457, 461, 463, 467,
  463, 461]

theorem chunk08 : ∀ j < 50, Brocard.recordOk (j + 408) (w08.getD j 0) = true := by
  decide +kernel

theorem chunk08_sound : ∀ n, 408 ≤ n → n < 458 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk08

end Brocard.WitnessData
