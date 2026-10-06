import Brocard.Witness

/-! Witness records n = 1339..1388 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w27 : List ℕ := [
  1367, 1367, 1361, 1367, 1367, 1361, 1367, 1361, 1367, 1367, 1373, 1367,
  1373, 1361, 1361, 1399, 1361, 1361, 1373, 1399, 1381, 1373, 1367, 1381,
  1367, 1373, 1373, 1381, 1373, 1381, 1423, 1373, 1373, 1399, 1399, 1399,
  1381, 1381, 1381, 1381, 1381, 1399, 1409, 1399, 1399, 1409, 1399, 1399,
  1399, 1399]

theorem chunk27 : ∀ j < 50, Brocard.recordOk (j + 1339) (w27.getD j 0) = true := by
  decide +kernel

theorem chunk27_sound : ∀ n, 1339 ≤ n → n < 1389 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk27

end Brocard.WitnessData
