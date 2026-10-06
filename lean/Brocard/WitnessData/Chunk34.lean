import Brocard.Witness

/-! Witness records n = 1689..1738 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w34 : List ℕ := [
  1709, 1693, 1693, 1697, 1723, 1709, 1783, 1699, 1699, 1721, 1709, 1721,
  1723, 1709, 1723, 1709, 1733, 1709, 1709, 1721, 1753, 1721, 1721, 1741,
  1721, 1741, 1721, 1723, 1723, 1733, 1723, 1723, 1723, 1733, 1741, 1733,
  1733, 1733, 1733, 1741, 1759, 1733, 1733, 1747, 1741, 1741, 1741, 1741,
  1753, 1741]

theorem chunk34 : ∀ j < 50, Brocard.recordOk (j + 1689) (w34.getD j 0) = true := by
  decide +kernel

theorem chunk34_sound : ∀ n, 1689 ≤ n → n < 1739 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk34

end Brocard.WitnessData
