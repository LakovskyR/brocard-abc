import Brocard.Witness

/-! Witness records n = 1789..1838 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w36 : List ℕ := [
  1801, 1811, 1801, 1801, 1823, 1811, 1823, 1801, 1823, 1823, 1811, 1823,
  1823, 1811, 1861, 1811, 1811, 1811, 1811, 1811, 1811, 1823, 1847, 1831,
  1823, 1847, 1823, 1823, 1823, 1823, 1831, 1831, 1847, 1847, 1831, 1847,
  1831, 1831, 1867, 1861, 1871, 1873, 1847, 1847, 1847, 1847, 1871, 1847,
  1847, 1847]

theorem chunk36 : ∀ j < 50, Brocard.recordOk (j + 1789) (w36.getD j 0) = true := by
  decide +kernel

theorem chunk36_sound : ∀ n, 1789 ≤ n → n < 1839 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk36

end Brocard.WitnessData
