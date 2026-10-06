import Brocard.Witness

/-! Witness records n = 758..807 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w15 : List ℕ := [
  821, 811, 787, 769, 797, 773, 769, 769, 773, 773, 773, 773,
  773, 773, 787, 787, 787, 809, 809, 787, 827, 787, 787, 787,
  797, 797, 787, 787, 797, 797, 809, 811, 797, 797, 797, 797,
  797, 797, 811, 811, 809, 811, 809, 839, 811, 809, 809, 809,
  811, 821]

theorem chunk15 : ∀ j < 50, Brocard.recordOk (j + 758) (w15.getD j 0) = true := by
  decide +kernel

theorem chunk15_sound : ∀ n, 758 ≤ n → n < 808 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk15

end Brocard.WitnessData
