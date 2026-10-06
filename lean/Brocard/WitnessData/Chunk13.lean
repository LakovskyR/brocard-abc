import Brocard.Witness

/-! Witness records n = 658..707 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w13 : List ℕ := [
  661, 661, 683, 673, 673, 677, 677, 673, 673, 673, 677, 683,
  683, 677, 677, 677, 677, 677, 683, 709, 701, 709, 683, 683,
  691, 701, 709, 701, 691, 701, 691, 691, 701, 701, 701, 709,
  701, 709, 701, 709, 701, 701, 719, 719, 709, 709, 719, 709,
  709, 709]

theorem chunk13 : ∀ j < 50, Brocard.recordOk (j + 658) (w13.getD j 0) = true := by
  decide +kernel

theorem chunk13_sound : ∀ n, 658 ≤ n → n < 708 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk13

end Brocard.WitnessData
