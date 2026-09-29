-- Prove2me | solution 1 for mme_released_recursive_global_window_center
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T17:15:52.52376+00:00
-- url     : https://prove2.me/submissions/8f4e2911-f99d-44c3-9ecd-daf56162c866

import Theorems.Thm_mme_released_recursive_profile_identity
import Theorems.Thm_mme_released_global_physical_orientation
open BigOperators MME MME.ReleasedGlobal MME.ReleasedMixture MME.RecursiveYZ
set_option autoImplicit false
set_option maxRecDepth 3000
attribute [local irreducible] alpha term parentProfile profile shapeEquiv roles hashMode

/-- The actual physical global window has exactly the primitive recursive
mixture as its center, for every histogram and every reference arrangement. -/
theorem solution (o : Fin 6) (k : ℕ) (eps : ℝ) (i : Fin 3)
    (mu : Cell 8 1 (fun _ _ ↦ 8) → Word → ℕ) :
    windowGood o k eps (hashMode o i) mu ↔
      ∀ c w, |(mu c w : ℝ) / (blocks k : ℝ) -
        ((alpha o (shapeEquiv.symm c.2) : ℝ) / D) *
          parentProfile (term o (shapeEquiv.symm c.2)) i w| ≤ eps := by
  have he (c : Cell 8 1 (fun _ _ ↦ 8)) (w : Word) :
      (profile o).2 (hashMode o i) c w =
        ((alpha o (shapeEquiv.symm c.2) : ℝ) / D) *
          parentProfile (term o (shapeEquiv.symm c.2)) i w := by
    rcases c with ⟨r,c⟩
    have hr : r = 0 := Fin.eq_zero r
    subst r
    have h := (mme_released_recursive_profile_identity o (hashMode o i) c w).2
    rw [(mme_released_global_physical_orientation.1 o i).1] at h
    exact h
  unfold windowGood
  simp only [he]
