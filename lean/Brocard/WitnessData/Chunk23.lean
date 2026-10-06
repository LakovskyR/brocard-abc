import Brocard.Witness

/-! Witness records n = 1139..1188 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w23 : List ℕ := [
  1163, 1153, 1151, 1151, 1153, 1151, 1171, 1151, 1153, 1181, 1153, 1163,
  1163, 1163, 1163, 1181, 1171, 1187, 1171, 1181, 1171, 1163, 1163, 1171,
  1171, 1171, 1181, 1201, 1171, 1171, 1171, 1187, 1181, 1181, 1181, 1181,
  1213, 1187, 1181, 1181, 1181, 1201, 1193, 1187, 1193, 1187, 1187, 1201,
  1213, 1231]

theorem chunk23 : ∀ j < 50, Brocard.recordOk (j + 1139) (w23.getD j 0) = true := by
  decide +kernel

theorem chunk23_sound : ∀ n, 1139 ≤ n → n < 1189 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk23

end Brocard.WitnessData
