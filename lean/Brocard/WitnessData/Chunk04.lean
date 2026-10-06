import Brocard.Witness

/-! Witness records n = 208..257 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w04 : List ℕ := [
  211, 211, 223, 229, 227, 223, 223, 223, 223, 227, 227, 223,
  233, 229, 227, 227, 227, 227, 229, 229, 233, 233, 251, 239,
  241, 241, 239, 239, 241, 241, 251, 251, 257, 269, 271, 257,
  269, 251, 251, 251, 251, 251, 257, 269, 257, 271, 263, 271,
  271, 263]

theorem chunk04 : ∀ j < 50, Brocard.recordOk (j + 208) (w04.getD j 0) = true := by
  decide +kernel

theorem chunk04_sound : ∀ n, 208 ≤ n → n < 258 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk04

end Brocard.WitnessData
