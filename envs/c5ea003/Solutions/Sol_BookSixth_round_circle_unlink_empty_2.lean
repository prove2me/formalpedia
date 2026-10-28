-- Prove2me | solution 2 for BookSixth.round_circle_unlink_empty
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-09-23T21:21:21.921973+00:00
-- url     : https://prove2.me/submissions/10fdbe8a-c048-4b2b-94e7-b0dfe81c0cdd

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

/-- The empty family is an unlink: the constant identity isotopy works, and the
condition on components is vacuous over `Fin 0`. -/
theorem BookSixth.round_circle_unlink_empty : IsUnlink (fun _ : Fin 0 => (∅ : Set Space3)) :=
  ⟨fun _ => Homeomorph.refl Space3,
    (Homeomorph.refl Space3).continuous.comp continuous_snd,
    (Homeomorph.refl Space3).symm.continuous.comp continuous_snd,
    fun _ => rfl,
    fun i => i.elim0⟩


-- Platform entry point: restates the target verbatim.
theorem _root_.solution : IsUnlink (fun _ : Fin 0 => (∅ : Set Space3)) := by
  apply @BookSixth.round_circle_unlink_empty <;> assumption
