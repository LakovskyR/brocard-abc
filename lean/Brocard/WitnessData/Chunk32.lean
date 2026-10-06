import Brocard.Witness

/-! Witness records n = 1589..1638 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w32 : List ℕ := [
  1597, 1601, 1607, 1619, 1597, 1597, 1597, 1607, 1607, 1613, 1609, 1621,
  1607, 1609, 1607, 1609, 1609, 1613, 1613, 1621, 1613, 1613, 1613, 1619,
  1619, 1657, 1621, 1619, 1619, 1621, 1621, 1637, 1627, 1637, 1637, 1627,
  1627, 1663, 1663, 1637, 1657, 1657, 1637, 1657, 1637, 1637, 1637, 1657,
  1657, 1663]

theorem chunk32 : ∀ j < 50, Brocard.recordOk (j + 1589) (w32.getD j 0) = true := by
  decide +kernel

theorem chunk32_sound : ∀ n, 1589 ≤ n → n < 1639 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk32

end Brocard.WitnessData
