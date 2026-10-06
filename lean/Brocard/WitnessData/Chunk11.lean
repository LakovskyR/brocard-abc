import Brocard.Witness

/-! Witness records n = 558..607 from certificates/witnesses_1_1038.jsonl
(SHA-256 d4d48938eb6b6ffa8eae345c3a03149d86b695b21843206ee9bf8adc17dad4dc). Generated. -/

namespace Brocard.WitnessData

def w11 : List ℕ := [
  563, 563, 563, 563, 569, 569, 577, 569, 577, 571, 571, 571,
  577, 577, 599, 577, 593, 587, 593, 607, 587, 587, 593, 593,
  593, 587, 587, 587, 601, 607, 593, 599, 601, 599, 601, 601,
  599, 599, 607, 601, 617, 607, 607, 619, 613, 607, 631, 613,
  613, 617]

theorem chunk11 : ∀ j < 50, Brocard.recordOk (j + 558) (w11.getD j 0) = true := by
  decide +kernel

theorem chunk11_sound : ∀ n, 558 ≤ n → n < 608 → ¬ ∃ m, n.factorial + 1 = m ^ 2 :=
  Brocard.chunk_sound chunk11

end Brocard.WitnessData
