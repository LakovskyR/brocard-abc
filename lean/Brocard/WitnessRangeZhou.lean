import Brocard.WitnessRange
import Brocard.WitnessData.Chunk21
import Brocard.WitnessData.Chunk22
import Brocard.WitnessData.Chunk23
import Brocard.WitnessData.Chunk24
import Brocard.WitnessData.Chunk25
import Brocard.WitnessData.Chunk26
import Brocard.WitnessData.Chunk27
import Brocard.WitnessData.Chunk28
import Brocard.WitnessData.Chunk29
import Brocard.WitnessData.Chunk30
import Brocard.WitnessData.Chunk31
import Brocard.WitnessData.Chunk32
import Brocard.WitnessData.Chunk33
import Brocard.WitnessData.Chunk34
import Brocard.WitnessData.Chunk35
import Brocard.WitnessData.Chunk36
import Brocard.WitnessData.Chunk37
import Brocard.WitnessData.Chunk38
import Brocard.WitnessData.Chunk39
import Brocard.WitnessData.Chunk40
import Brocard.WitnessData.Chunk41

/-! The additional 1009 witness records for the Zhou proof, in 21 chunks. -/

open Nat

namespace Brocard

theorem zhou_witness_range : ∀ n, 1039 ≤ n → n < 2048 → ¬ ∃ m, n ! + 1 = m ^ 2 := by
  apply range_glue WitnessData.chunk21_sound
  apply range_glue WitnessData.chunk22_sound
  apply range_glue WitnessData.chunk23_sound
  apply range_glue WitnessData.chunk24_sound
  apply range_glue WitnessData.chunk25_sound
  apply range_glue WitnessData.chunk26_sound
  apply range_glue WitnessData.chunk27_sound
  apply range_glue WitnessData.chunk28_sound
  apply range_glue WitnessData.chunk29_sound
  apply range_glue WitnessData.chunk30_sound
  apply range_glue WitnessData.chunk31_sound
  apply range_glue WitnessData.chunk32_sound
  apply range_glue WitnessData.chunk33_sound
  apply range_glue WitnessData.chunk34_sound
  apply range_glue WitnessData.chunk35_sound
  apply range_glue WitnessData.chunk36_sound
  apply range_glue WitnessData.chunk37_sound
  apply range_glue WitnessData.chunk38_sound
  apply range_glue WitnessData.chunk39_sound
  apply range_glue WitnessData.chunk40_sound
  exact WitnessData.chunk41_sound

/-- Additional certificate range: no solution for `1039 ≤ n ≤ 2047`. -/
theorem no_solution_1039_to_2047 : ∀ n, 1039 ≤ n → n ≤ 2047 → ¬ ∃ m, n ! + 1 = m ^ 2 :=
  fun n h1039 h2047 => zhou_witness_range n h1039 (by omega)

/-- Complete certificate range below the Zhou tail. -/
theorem no_solution_8_to_2047 : ∀ n, 8 ≤ n → n ≤ 2047 → ¬ ∃ m, n ! + 1 = m ^ 2 := by
  intro n h8 h2047
  by_cases h1038 : n ≤ 1038
  · exact no_solution_8_to_1038 n h8 h1038
  · exact no_solution_1039_to_2047 n (by omega) h2047

end Brocard
