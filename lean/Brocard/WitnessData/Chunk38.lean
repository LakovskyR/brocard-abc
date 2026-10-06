import Brocard.Witness

/-! Witness records n = 1889..1938 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w38 : List ℕ := [
  1901, 1913, 1901, 1901, 1907, 1901, 1913, 1901, 1907, 1901, 1901, 1907,
  1913, 1907, 1907, 1907, 1907, 1931, 1931, 1913, 1913, 1973, 1949, 1931,
  1931, 1973, 1931, 1933, 1931, 1933, 1933, 1931, 1933, 1973, 1949, 1933,
  1931, 1931, 1931, 1931, 1931, 1933, 1933, 1951, 1949, 1949, 1949, 1949,
  1951, 1951]

theorem chunk38 : ∀ j < 50, Brocard.recordOk (j + 1889) (w38.getD j 0) = true := by
  decide +kernel

theorem chunk38_sound : ∀ n, 1889 ≤ n → n < 1939 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk38

end Brocard.WitnessData
