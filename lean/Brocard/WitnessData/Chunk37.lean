import Brocard.Witness

/-! Witness records n = 1839..1888 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w37 : List ℕ := [
  1847, 1847, 1847, 1873, 1861, 1861, 1867, 1861, 1861, 1867, 1867, 1861,
  1877, 1861, 1861, 1861, 1861, 1867, 1867, 1861, 1861, 1867, 1867, 1867,
  1871, 1867, 1867, 1871, 1871, 1873, 1877, 1907, 1877, 1877, 1879, 1877,
  1877, 1889, 1889, 1901, 1901, 1889, 1889, 1913, 1889, 1889, 1901, 1901,
  1901, 1907]

theorem chunk37 : ∀ j < 50, Brocard.recordOk (j + 1839) (w37.getD j 0) = true := by
  decide +kernel

theorem chunk37_sound : ∀ n, 1839 ≤ n → n < 1889 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk37

end Brocard.WitnessData
