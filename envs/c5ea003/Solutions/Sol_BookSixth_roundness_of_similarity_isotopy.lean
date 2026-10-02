-- Prove2me | solution 1 for BookSixth.roundness_of_similarity_isotopy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T17:56:58.308101+00:00
-- url     : https://prove2.me/submissions/d1b54d6f-b0c5-48e6-bf8e-d6f277b0e7df

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_similarity_preserves_roundness

open scoped BigOperators
open BookSixth

/-- A family of positive similarities keeps a round circle round at every time. This is
the time-indexed form of the proved pointwise theorem: each `G t` is `a t • x + b t`
with `a t > 0`, so applying the pointwise result at each `t` gives the conclusion
directly, with the hypothesis turned into an image equality by `Set.image_congr'`. -/
theorem solution {C : Set Space3} (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hsim : ∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (G t) x = (q.1 • x) + q.2)) :
    ∀ t, RoundCircle ((G t) '' C) := by
  intro t
  obtain ⟨⟨a, b⟩, ha, hmap⟩ := hsim t
  have hEq : ((fun x : Space3 => a • x + b) '' C) = (G t) '' C :=
    Set.image_congr' (fun x : Space3 => (hmap x).symm)
  rw [← hEq]
  exact BookSixth.similarity_preserves_roundness C a b ha hC
