import Brocard.Witness

/-! Witness records n = 1239..1288 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w25 : List ℕ := [
  1249, 1249, 1249, 1249, 1289, 1249, 1249, 1259, 1259, 1277, 1259, 1277,
  1279, 1259, 1259, 1259, 1259, 1259, 1259, 1277, 1277, 1277, 1277, 1277,
  1277, 1279, 1279, 1277, 1277, 1279, 1283, 1277, 1277, 1279, 1277, 1277,
  1277, 1283, 1289, 1291, 1289, 1283, 1283, 1289, 1289, 1289, 1289, 1291,
  1301, 1291]

theorem chunk25 : ∀ j < 50, Brocard.recordOk (j + 1239) (w25.getD j 0) = true := by
  decide +kernel

theorem chunk25_sound : ∀ n, 1239 ≤ n → n < 1289 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk25

end Brocard.WitnessData
