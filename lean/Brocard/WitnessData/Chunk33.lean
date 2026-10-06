import Brocard.Witness

/-! Witness records n = 1639..1688 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w33 : List ℕ := [
  1657, 1657, 1657, 1657, 1693, 1663, 1657, 1657, 1667, 1663, 1667, 1669,
  1657, 1667, 1657, 1663, 1693, 1667, 1667, 1663, 1693, 1667, 1669, 1667,
  1669, 1667, 1667, 1669, 1669, 1693, 1709, 1699, 1699, 1693, 1693, 1699,
  1693, 1721, 1693, 1697, 1693, 1697, 1693, 1721, 1697, 1693, 1699, 1699,
  1697, 1697]

theorem chunk33 : ∀ j < 50, Brocard.recordOk (j + 1639) (w33.getD j 0) = true := by
  decide +kernel

theorem chunk33_sound : ∀ n, 1639 ≤ n → n < 1689 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk33

end Brocard.WitnessData
