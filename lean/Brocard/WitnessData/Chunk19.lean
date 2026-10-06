import Brocard.Witness

/-! Witness records n = 958..1007 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w19 : List ℕ := [
  971, 971, 971, 1009, 983, 991, 971, 971, 971, 971, 971, 971,
  983, 1009, 983, 977, 983, 983, 983, 983, 991, 991, 991, 997,
  991, 991, 997, 991, 1009, 997, 1031, 1009, 1013, 1021, 997, 1009,
  997, 997, 1019, 1013, 1039, 1009, 1013, 1019, 1013, 1031, 1009, 1019,
  1013, 1013]

theorem chunk19 : ∀ j < 50, Brocard.recordOk (j + 958) (w19.getD j 0) = true := by
  decide +kernel

theorem chunk19_sound : ∀ n, 958 ≤ n → n < 1008 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk19

end Brocard.WitnessData
