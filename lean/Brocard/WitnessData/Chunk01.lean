import Brocard.Witness

/-! Witness records n = 58..107 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w01 : List ℕ := [
  61, 61, 67, 67, 89, 67, 67, 67, 71, 71, 79, 73,
  83, 79, 83, 79, 79, 83, 97, 89, 83, 83, 83, 83,
  89, 89, 97, 103, 101, 101, 101, 101, 101, 97, 97, 97,
  101, 103, 107, 101, 101, 101, 139, 113, 107, 109, 107, 107,
  109, 109]

theorem chunk01 : ∀ j < 50, Brocard.recordOk (j + 58) (w01.getD j 0) = true := by
  decide +kernel

theorem chunk01_sound : ∀ n, 58 ≤ n → n < 108 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk01

end Brocard.WitnessData
