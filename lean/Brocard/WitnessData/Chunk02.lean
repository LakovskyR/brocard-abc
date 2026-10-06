import Brocard.Witness

/-! Witness records n = 108..157 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w02 : List ℕ := [
  127, 113, 137, 131, 127, 127, 139, 151, 131, 131, 137, 149,
  127, 131, 131, 137, 139, 131, 137, 131, 131, 131, 137, 149,
  157, 137, 139, 151, 139, 139, 151, 173, 151, 163, 151, 151,
  149, 151, 149, 149, 157, 163, 173, 193, 163, 163, 157, 157,
  173, 163]

theorem chunk02 : ∀ j < 50, Brocard.recordOk (j + 108) (w02.getD j 0) = true := by
  decide +kernel

theorem chunk02_sound : ∀ n, 108 ≤ n → n < 158 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk02

end Brocard.WitnessData
