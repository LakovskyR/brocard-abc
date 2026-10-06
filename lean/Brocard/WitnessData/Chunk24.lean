import Brocard.Witness

/-! Witness records n = 1189..1238 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w24 : List ℕ := [
  1229, 1231, 1201, 1213, 1213, 1213, 1217, 1201, 1223, 1223, 1223, 1217,
  1213, 1223, 1213, 1217, 1213, 1217, 1217, 1229, 1213, 1213, 1213, 1223,
  1229, 1223, 1223, 1229, 1223, 1223, 1231, 1229, 1237, 1229, 1289, 1229,
  1231, 1229, 1229, 1259, 1259, 1237, 1259, 1237, 1249, 1237, 1237, 1249,
  1277, 1279]

theorem chunk24 : ∀ j < 50, Brocard.recordOk (j + 1189) (w24.getD j 0) = true := by
  decide +kernel

theorem chunk24_sound : ∀ n, 1189 ≤ n → n < 1239 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk24

end Brocard.WitnessData
