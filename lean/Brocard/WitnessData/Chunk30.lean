import Brocard.Witness

/-! Witness records n = 1489..1538 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w30 : List ℕ := [
  1511, 1493, 1493, 1499, 1499, 1523, 1511, 1499, 1499, 1511, 1511, 1511,
  1511, 1511, 1559, 1523, 1523, 1511, 1523, 1523, 1531, 1531, 1549, 1523,
  1523, 1523, 1531, 1523, 1531, 1523, 1531, 1523, 1523, 1531, 1549, 1531,
  1549, 1531, 1543, 1531, 1531, 1549, 1543, 1549, 1543, 1553, 1543, 1567,
  1549, 1553]

theorem chunk30 : ∀ j < 50, Brocard.recordOk (j + 1489) (w30.getD j 0) = true := by
  decide +kernel

theorem chunk30_sound : ∀ n, 1489 ≤ n → n < 1539 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk30

end Brocard.WitnessData
