import Brocard.Witness

/-! Witness records n = 1289..1338 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w26 : List ℕ := [
  1291, 1297, 1297, 1301, 1301, 1301, 1307, 1303, 1301, 1301, 1301, 1319,
  1319, 1307, 1307, 1307, 1307, 1321, 1319, 1319, 1319, 1319, 1367, 1319,
  1321, 1319, 1327, 1321, 1321, 1327, 1427, 1327, 1361, 1361, 1367, 1361,
  1367, 1361, 1373, 1367, 1373, 1373, 1361, 1361, 1361, 1433, 1367, 1361,
  1367, 1399]

theorem chunk26 : ∀ j < 50, Brocard.recordOk (j + 1289) (w26.getD j 0) = true := by
  decide +kernel

theorem chunk26_sound : ∀ n, 1289 ≤ n → n < 1339 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk26

end Brocard.WitnessData
