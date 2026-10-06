import Brocard.Witness

/-! Witness records n = 858..907 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w17 : List ℕ := [
  863, 863, 887, 881, 881, 877, 883, 881, 881, 877, 887, 877,
  881, 887, 877, 877, 877, 877, 883, 883, 883, 883, 883, 883,
  887, 907, 907, 919, 907, 911, 941, 911, 907, 919, 907, 907,
  937, 907, 907, 907, 907, 911, 907, 907, 929, 907, 907, 907,
  919, 911]

theorem chunk17 : ∀ j < 50, Brocard.recordOk (j + 858) (w17.getD j 0) = true := by
  decide +kernel

theorem chunk17_sound : ∀ n, 858 ≤ n → n < 908 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk17

end Brocard.WitnessData
