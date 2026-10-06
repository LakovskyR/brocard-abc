import Brocard.Witness

/-! Witness records n = 608..657 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w12 : List ℕ := [
  631, 613, 613, 613, 631, 617, 631, 631, 619, 619, 631, 631,
  647, 641, 631, 631, 631, 631, 631, 641, 691, 641, 643, 641,
  643, 647, 641, 641, 647, 641, 653, 647, 643, 643, 647, 653,
  661, 653, 653, 653, 659, 659, 653, 653, 661, 659, 659, 661,
  659, 659]

theorem chunk12 : ∀ j < 50, Brocard.recordOk (j + 608) (w12.getD j 0) = true := by
  decide +kernel

theorem chunk12_sound : ∀ n, 608 ≤ n → n < 658 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk12

end Brocard.WitnessData
