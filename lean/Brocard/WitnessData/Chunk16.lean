import Brocard.Witness

/-! Witness records n = 808..857 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w16 : List ℕ := [
  811, 811, 821, 821, 829, 823, 821, 827, 827, 827, 821, 821,
  829, 829, 827, 829, 827, 827, 829, 829, 839, 877, 853, 853,
  839, 859, 857, 853, 853, 857, 853, 859, 853, 863, 859, 857,
  853, 857, 857, 859, 853, 863, 853, 853, 857, 881, 859, 877,
  859, 859]

theorem chunk16 : ∀ j < 50, Brocard.recordOk (j + 808) (w16.getD j 0) = true := by
  decide +kernel

theorem chunk16_sound : ∀ n, 808 ≤ n → n < 858 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk16

end Brocard.WitnessData
