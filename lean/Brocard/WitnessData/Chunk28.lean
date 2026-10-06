import Brocard.Witness

/-! Witness records n = 1389..1438 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w28 : List ℕ := [
  1399, 1399, 1409, 1423, 1399, 1399, 1399, 1423, 1423, 1427, 1409, 1409,
  1439, 1409, 1409, 1409, 1409, 1423, 1427, 1427, 1423, 1447, 1427, 1423,
  1429, 1423, 1427, 1423, 1427, 1423, 1427, 1429, 1447, 1429, 1427, 1427,
  1427, 1429, 1429, 1439, 1439, 1439, 1439, 1439, 1447, 1439, 1439, 1447,
  1447, 1447]

theorem chunk28 : ∀ j < 50, Brocard.recordOk (j + 1389) (w28.getD j 0) = true := by
  decide +kernel

theorem chunk28_sound : ∀ n, 1389 ≤ n → n < 1439 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk28

end Brocard.WitnessData
