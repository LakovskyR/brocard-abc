import Brocard.Witness

/-! Witness records n = 1039..1088 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w21 : List ℕ := [
  1049, 1051, 1049, 1049, 1049, 1051, 1087, 1051, 1051, 1051, 1051, 1061,
  1061, 1061, 1063, 1061, 1063, 1063, 1087, 1061, 1061, 1069, 1069, 1091,
  1069, 1103, 1087, 1069, 1069, 1087, 1087, 1091, 1091, 1091, 1087, 1097,
  1093, 1087, 1087, 1103, 1091, 1087, 1109, 1103, 1093, 1091, 1091, 1091,
  1091, 1091]

theorem chunk21 : ∀ j < 50, Brocard.recordOk (j + 1039) (w21.getD j 0) = true := by
  decide +kernel

theorem chunk21_sound : ∀ n, 1039 ≤ n → n < 1089 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk21

end Brocard.WitnessData
