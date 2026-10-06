import Brocard.Witness

/-! Witness records n = 708..757 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w14 : List ℕ := [
  733, 719, 719, 757, 727, 727, 719, 727, 727, 733, 727, 727,
  743, 733, 727, 727, 733, 739, 733, 739, 739, 739, 733, 733,
  739, 751, 739, 739, 739, 739, 757, 743, 761, 751, 761, 751,
  751, 751, 751, 761, 757, 757, 761, 761, 773, 757, 757, 757,
  761, 769]

theorem chunk14 : ∀ j < 50, Brocard.recordOk (j + 708) (w14.getD j 0) = true := by
  decide +kernel

theorem chunk14_sound : ∀ n, 708 ≤ n → n < 758 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk14

end Brocard.WitnessData
