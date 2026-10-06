import Brocard.Witness

/-! Witness records n = 158..207 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w03 : List ℕ := [
  163, 163, 163, 163, 167, 173, 173, 181, 179, 173, 181, 173,
  173, 173, 193, 179, 193, 181, 179, 179, 181, 181, 193, 191,
  191, 191, 191, 193, 199, 191, 197, 197, 211, 197, 223, 199,
  197, 197, 227, 211, 211, 239, 211, 223, 211, 211, 211, 227,
  211, 211]

theorem chunk03 : ∀ j < 50, Brocard.recordOk (j + 158) (w03.getD j 0) = true := by
  decide +kernel

theorem chunk03_sound : ∀ n, 158 ≤ n → n < 208 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk03

end Brocard.WitnessData
