import Brocard.Witness

/-! Witness records n = 1008..1038 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w20 : List ℕ := [
  1031, 1013, 1013, 1013, 1019, 1019, 1019, 1021, 1019, 1019, 1021, 1021,
  1033, 1031, 1031, 1031, 1031, 1033, 1039, 1031, 1033, 1039, 1049, 1049,
  1039, 1039, 1063, 1039, 1049, 1051, 1061]

theorem chunk20 : ∀ j < 31, Brocard.recordOk (j + 1008) (w20.getD j 0) = true := by
  decide +kernel

theorem chunk20_sound : ∀ n, 1008 ≤ n → n < 1039 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk20

end Brocard.WitnessData
