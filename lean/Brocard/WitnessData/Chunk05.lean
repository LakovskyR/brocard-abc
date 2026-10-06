import Brocard.Witness

/-! Witness records n = 258..307 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w05 : List ℕ := [
  269, 263, 269, 269, 269, 293, 283, 269, 269, 269, 311, 277,
  277, 281, 277, 277, 277, 277, 307, 281, 311, 307, 283, 283,
  293, 311, 293, 307, 293, 293, 293, 293, 293, 293, 311, 307,
  311, 307, 307, 331, 311, 307, 307, 307, 307, 331, 307, 307,
  311, 313]

theorem chunk05 : ∀ j < 50, Brocard.recordOk (j + 258) (w05.getD j 0) = true := by
  decide +kernel

theorem chunk05_sound : ∀ n, 258 ≤ n → n < 308 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk05

end Brocard.WitnessData
