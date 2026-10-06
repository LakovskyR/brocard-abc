import Brocard.Witness

/-! Witness records n = 1539..1588 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w31 : List ℕ := [
  1543, 1549, 1559, 1567, 1549, 1549, 1549, 1549, 1549, 1553, 1559, 1571,
  1597, 1559, 1571, 1559, 1579, 1567, 1567, 1567, 1567, 1567, 1579, 1571,
  1567, 1579, 1571, 1571, 1571, 1571, 1571, 1583, 1579, 1583, 1597, 1583,
  1579, 1579, 1579, 1597, 1583, 1601, 1597, 1597, 1597, 1609, 1619, 1601,
  1609, 1601]

theorem chunk31 : ∀ j < 50, Brocard.recordOk (j + 1539) (w31.getD j 0) = true := by
  decide +kernel

theorem chunk31_sound : ∀ n, 1539 ≤ n → n < 1589 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk31

end Brocard.WitnessData
