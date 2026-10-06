import Brocard.Witness

/-! Witness records n = 1989..2038 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w40 : List ℕ := [
  1993, 1999, 1997, 1997, 1999, 1997, 1997, 2017, 2027, 2017, 2027, 2003,
  2003, 2011, 2011, 2011, 2017, 2029, 2011, 2011, 2011, 2053, 2017, 2039,
  2027, 2027, 2063, 2027, 2027, 2063, 2029, 2027, 2029, 2029, 2029, 2027,
  2027, 2029, 2029, 2053, 2039, 2063, 2039, 2053, 2063, 2081, 2039, 2063,
  2053, 2053]

theorem chunk40 : ∀ j < 50, Brocard.recordOk (j + 1989) (w40.getD j 0) = true := by
  decide +kernel

theorem chunk40_sound : ∀ n, 1989 ≤ n → n < 2039 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk40

end Brocard.WitnessData
