-- Prove2me | Theorems.Thm_mme_regional_tolerance_window_log_recipe_descent
-- name    : mme_regional_tolerance_window_log_recipe_descent
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T21:24:56.74971+00:00
-- url     : https://prove2.me/theorems/ed3e269b-d388-474b-ba3d-35ffae3b4bfe
-- title:
--   Tolerance windows extend finite logarithmic regional recipes
-- statement:
--   Every lower-stage logarithmic regional recipe on a child tolerance window extends to a higher-stage recipe on the common enlarged parent window, assuming only the explicit finite size test and a uniform scalar log-copy budget. The resulting input cost is at most the polynomial number of exact types times the child input cost, its guaranteed log output increases by the specified rate, and its matrix dimensions are unchanged.
-- source:
--   Finite physical tolerance-window extraction for the More Asymmetry proof.

import Theorems.Thm_mme_regional_tolerance_window_step_family
import Definitions.Def_mme_logarithmic_regional_CW_recipe
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem mme_regional_tolerance_window_log_recipe_descent {ell upper M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell < upper) (delta eps rate : ℝ)
    (hdelta : 0 ≤ delta) (heps : 0 < eps) (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤ (D.minimum : ℝ) * eps^2)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) → rate ≤ windowLogBudget D mu eps)
    (next : LogRecipe M ell (childWindow D delta)) :
    ∃ E : LogRecipe M upper (parentWindow D (eps+2*delta)),
      E.inputs ≤ ((Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) * Fintype.card (CompleteWord ell))) * next.inputs ∧
      E.logOutputs = rate + next.logOutputs ∧ E.dims = next.dims := by
  sorry
