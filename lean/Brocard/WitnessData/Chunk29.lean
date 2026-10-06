import Brocard.Witness

/-! Witness records n = 1439..1488 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w29 : List ℕ := [
  1447, 1453, 1453, 1447, 1447, 1451, 1451, 1453, 1471, 1451, 1451, 1453,
  1453, 1459, 1471, 1471, 1487, 1459, 1459, 1471, 1471, 1471, 1471, 1471,
  1471, 1487, 1471, 1471, 1481, 1483, 1481, 1483, 1483, 1483, 1483, 1481,
  1481, 1481, 1481, 1493, 1487, 1483, 1483, 1489, 1511, 1489, 1489, 1499,
  1493, 1493]

theorem chunk29 : ∀ j < 50, Brocard.recordOk (j + 1439) (w29.getD j 0) = true := by
  decide +kernel

theorem chunk29_sound : ∀ n, 1439 ≤ n → n < 1489 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk29

end Brocard.WitnessData
