-- Prove2me | solution 1 for SheafCohomologyRobustness.NerveBetti.const_along_walk
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T16:08:36.670494+00:00
-- url     : https://prove2.me/submissions/801bd697-c557-491a-81a0-f09d8f739eb8

import Mathlib
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_GraphNervePoincare
import Definitions.Def_MachineLearning_SheafCohomologyRobustness_NerveBetti
open Finset SheafCohomologyRobustness NerveBetti GraphNerve in
theorem solution {ι Edge : Type*} (G : NerveGraph ι Edge) {f : ι → ℝ}
    (hf : ∀ e : Edge, f (G.tgt e) = f (G.src e)) :
    ∀ (i : ι) (l : List ι), IsWalk (edgeAdj G) i l → f (endpt i l) = f i := by
  intro i l
  induction l generalizing i with
  | nil => intro _; rfl
  | cons j t ih =>
    rintro ⟨hij, ht⟩
    -- `f` agrees across every overlap, in either orientation
    have hstep : f j = f i := by
      obtain ⟨e, ⟨hs, ht'⟩ | ⟨hs, ht'⟩⟩ := hij
      · rw [← ht', ← hs]; exact hf e
      · rw [← ht', ← hs]; exact (hf e).symm
    show f (endpt j t) = f i
    rw [ih j ht, hstep]
