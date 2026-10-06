import Brocard.WitnessData.Chunk00
import Brocard.WitnessData.Chunk01
import Brocard.WitnessData.Chunk02
import Brocard.WitnessData.Chunk03
import Brocard.WitnessData.Chunk04
import Brocard.WitnessData.Chunk05
import Brocard.WitnessData.Chunk06
import Brocard.WitnessData.Chunk07
import Brocard.WitnessData.Chunk08
import Brocard.WitnessData.Chunk09
import Brocard.WitnessData.Chunk10
import Brocard.WitnessData.Chunk11
import Brocard.WitnessData.Chunk12
import Brocard.WitnessData.Chunk13
import Brocard.WitnessData.Chunk14
import Brocard.WitnessData.Chunk15
import Brocard.WitnessData.Chunk16
import Brocard.WitnessData.Chunk17
import Brocard.WitnessData.Chunk18
import Brocard.WitnessData.Chunk19
import Brocard.WitnessData.Chunk20

/-! Glue of the 21 witness chunks: the certificate half. Generated. -/

open Nat

namespace Brocard

theorem witness_range : ∀ n, 8 ≤ n → n < 1039 → ¬ ∃ m, n ! + 1 = m ^ 2 :=
  range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (range_glue (WitnessData.chunk00_sound) WitnessData.chunk01_sound) WitnessData.chunk02_sound) WitnessData.chunk03_sound) WitnessData.chunk04_sound) WitnessData.chunk05_sound) WitnessData.chunk06_sound) WitnessData.chunk07_sound) WitnessData.chunk08_sound) WitnessData.chunk09_sound) WitnessData.chunk10_sound) WitnessData.chunk11_sound) WitnessData.chunk12_sound) WitnessData.chunk13_sound) WitnessData.chunk14_sound) WitnessData.chunk15_sound) WitnessData.chunk16_sound) WitnessData.chunk17_sound) WitnessData.chunk18_sound) WitnessData.chunk19_sound) WitnessData.chunk20_sound

/-- Certificate half: no solution for `8 ≤ n ≤ 1038`. -/
theorem no_solution_8_to_1038 : ∀ n, 8 ≤ n → n ≤ 1038 → ¬ ∃ m, n ! + 1 = m ^ 2 :=
  fun n h8 h1038 => witness_range n h8 (by omega)

end Brocard
