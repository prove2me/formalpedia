-- Prove2me | Theorems.Thm_mme_integer_step_child_window_boundary_recipe
-- name    : mme_integer_step_child_window_boundary_recipe
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:11:04.666779+00:00
-- url     : https://prove2.me/theorems/96e9c254-e4cd-49d0-8428-ed42de318ffa
-- title:
--   Exact boundary profiles give terminal child-window recipes
-- statement:
--   Let $D$ be an integer regional extraction step and partition its physical positions into reference cells. Suppose every cell has a mode of grade zero. For every $\delta\ge0$, the child-frequency window of radius $\delta$ admits a terminal logarithmic recipe with one input and logarithmic output budget zero. The construction retains oriented boundary profiles reproducing all cell grades and all mode histograms. Each matrix dimension is the product of the corresponding oriented profile dimensions. This supplies a terminal child-window recipe at any depth satisfying the zero-mode condition.
-- source:
--   Exact integer regional profiles, tolerance windows and terminal CW recipes.

import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_integer_step_child_window_boundary_recipe
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (hz : ∀ j, ∃ z : Fin 3, ((part.cells j).2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogRecipe M ell (childWindow D delta),
        E.inputs = 1 ∧ E.logOutputs = 0 ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by sorry
