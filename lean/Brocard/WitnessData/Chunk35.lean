import Brocard.Witness

/-! Witness records n = 1739..1788 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w35 : List ℕ := [
  1741, 1753, 1747, 1759, 1747, 1747, 1747, 1753, 1753, 1753, 1753, 1759,
  1759, 1759, 1759, 1759, 1783, 1777, 1783, 1777, 1787, 1777, 1783, 1777,
  1777, 1787, 1787, 1777, 1783, 1783, 1787, 1777, 1777, 1787, 1777, 1783,
  1783, 1783, 1787, 1789, 1783, 1787, 1801, 1861, 1789, 1787, 1787, 1789,
  1789, 1811]

theorem chunk35 : ∀ j < 50, Brocard.recordOk (j + 1739) (w35.getD j 0) = true := by
  decide +kernel

theorem chunk35_sound : ∀ n, 1739 ≤ n → n < 1789 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk35

end Brocard.WitnessData
