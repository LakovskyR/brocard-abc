import Brocard.Witness

/-! Witness records n = 508..557 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w10 : List ℕ := [
  521, 541, 547, 521, 521, 521, 523, 521, 523, 523, 557, 547,
  523, 523, 541, 541, 541, 547, 557, 547, 569, 541, 557, 541,
  541, 547, 557, 541, 541, 541, 541, 541, 571, 547, 547, 547,
  547, 547, 557, 557, 557, 557, 563, 557, 557, 569, 557, 557,
  563, 569]

theorem chunk10 : ∀ j < 50, Brocard.recordOk (j + 508) (w10.getD j 0) = true := by
  decide +kernel

theorem chunk10_sound : ∀ n, 508 ≤ n → n < 558 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk10

end Brocard.WitnessData
