import Brocard.Witness

/-! Witness records n = 908..957 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w18 : List ℕ := [
  937, 919, 929, 919, 919, 919, 919, 937, 947, 947, 929, 937,
  929, 929, 937, 929, 929, 937, 947, 947, 937, 941, 941, 937,
  937, 937, 953, 947, 941, 941, 941, 941, 947, 967, 977, 953,
  947, 947, 953, 967, 967, 953, 971, 983, 967, 971, 971, 967,
  971, 977]

theorem chunk18 : ∀ j < 50, Brocard.recordOk (j + 908) (w18.getD j 0) = true := by
  decide +kernel

theorem chunk18_sound : ∀ n, 908 ≤ n → n < 958 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk18

end Brocard.WitnessData
