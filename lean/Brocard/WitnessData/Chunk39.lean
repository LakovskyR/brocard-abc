import Brocard.Witness

/-! Witness records n = 1939..1988 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w39 : List ℕ := [
  1951, 1949, 1949, 1949, 1979, 1949, 1949, 1949, 1949, 1973, 1973, 1979,
  1973, 1979, 1993, 1973, 1997, 1979, 1973, 1973, 1979, 1973, 1979, 1973,
  1973, 1979, 1979, 1973, 1973, 1979, 1973, 1973, 1973, 1979, 1979, 2027,
  1979, 1979, 1979, 1993, 1987, 1993, 1987, 1987, 1993, 1987, 1987, 1993,
  1993, 1993]

theorem chunk39 : ∀ j < 50, Brocard.recordOk (j + 1939) (w39.getD j 0) = true := by
  decide +kernel

theorem chunk39_sound : ∀ n, 1939 ≤ n → n < 1989 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk39

end Brocard.WitnessData
