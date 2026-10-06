import Brocard.Witness

/-! Witness records n = 308..357 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w06 : List ℕ := [
  313, 313, 317, 317, 331, 347, 317, 317, 331, 331, 331, 331,
  331, 349, 359, 331, 331, 337, 331, 331, 331, 331, 347, 337,
  337, 359, 359, 347, 349, 349, 347, 349, 347, 349, 349, 349,
  347, 347, 349, 349, 353, 367, 359, 359, 373, 367, 367, 359,
  379, 373]

theorem chunk06 : ∀ j < 50, Brocard.recordOk (j + 308) (w06.getD j 0) = true := by
  decide +kernel

theorem chunk06_sound : ∀ n, 308 ≤ n → n < 358 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk06

end Brocard.WitnessData
