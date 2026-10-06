import Brocard.Witness

/-! Witness records n = 1089..1138 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w22 : List ℕ := [
  1091, 1093, 1093, 1097, 1103, 1103, 1123, 1109, 1103, 1151, 1103, 1109,
  1109, 1129, 1117, 1109, 1109, 1109, 1109, 1153, 1117, 1123, 1129, 1117,
  1117, 1117, 1117, 1123, 1123, 1129, 1129, 1123, 1123, 1129, 1151, 1153,
  1163, 1153, 1163, 1151, 1151, 1151, 1151, 1153, 1181, 1153, 1151, 1171,
  1153, 1163]

theorem chunk22 : ∀ j < 50, Brocard.recordOk (j + 1089) (w22.getD j 0) = true := by
  decide +kernel

theorem chunk22_sound : ∀ n, 1089 ≤ n → n < 1139 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk22

end Brocard.WitnessData
