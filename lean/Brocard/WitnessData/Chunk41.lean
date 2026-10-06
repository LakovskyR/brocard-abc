import Brocard.Witness

/-! Witness records n = 2039..2047 from certificates/witnesses_1_2047.jsonl
(SHA-256 3f17cc47130b9eaf2c63ae8cb0d5300e6b8e801e38441b93a6897e3ffa472758). Generated. -/

namespace Brocard.WitnessData

def w41 : List ℕ := [
  2069, 2063, 2063, 2053, 2053, 2063, 2053, 2069, 2069]

theorem chunk41 : ∀ j < 9, Brocard.recordOk (j + 2039) (w41.getD j 0) = true := by
  decide +kernel

theorem chunk41_sound : ∀ n, 2039 ≤ n → n < 2048 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk41

end Brocard.WitnessData
