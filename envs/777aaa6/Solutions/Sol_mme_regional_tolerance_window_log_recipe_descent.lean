-- Prove2me | solution 1 for mme_regional_tolerance_window_log_recipe_descent
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T21:26:01.171552+00:00
-- url     : https://prove2.me/submissions/40fa2788-321a-4f18-a4a1-0d9219ab4991

import Theorems.Thm_mme_regional_tolerance_window_step_family
import Definitions.Def_mme_logarithmic_regional_CW_recipe
open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem solution {ell upper M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
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
  obtain ⟨types,steps,hpoly,hbud,hinside,hcover⟩ :=
    mme_regional_tolerance_window_step_family D delta eps rate hdelta heps hsize hbudget
  refine ⟨LogRecipe.descend hlevel types rate hrate steps hbud hinside hcover next,?_,rfl,rfl⟩
  exact Nat.mul_le_mul_right next.inputs hpoly
