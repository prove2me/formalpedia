-- Prove2me | Theorems.Thm_mme_joint_regional_tolerance_window_log_recipe_descent
-- name    : mme_joint_regional_tolerance_window_log_recipe_descent
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:40:57.963985+00:00
-- url     : https://prove2.me/theorems/c50bed9f-9ac0-493f-99a4-af707bfe255d
-- title:
--   Simultaneous regional tolerance-window descent
-- statement:
--   Partition the coordinate positions into finitely many regions $j$. In each region choose an integer extraction step, tolerances $\delta_j\ge0$ and $\varepsilon_j>0$, and a nonnegative rate $r_j$ satisfying the scalar size test and the explicit window budget uniformly over all admissible profiles within $\delta_j$ of the central profile. Let
--   \[
--   H_j=(|\operatorname{Position}_j|+1)^{3|\operatorname{Cell}_j||\operatorname{CompleteWord}_{\ell}|}.
--   \]
--   Suppose the product of the regional parent windows of radii $\varepsilon_j+2\delta_j$ lies in the source predicate, and the predicate of a shared lower-level joint recipe $F$ lies in every corresponding child window. At any strictly higher level there exists a joint recipe $E$ with
--   \[
--   \operatorname{inputs}(E)\le\Bigl(\prod_j H_j\Bigr)\operatorname{inputs}(F),\qquad
--   \operatorname{logOutputs}(E)=\sum_j r_j+\operatorname{logOutputs}(F),\qquad
--   \operatorname{dims}(E)=\operatorname{dims}(F).
--   \]
--   The lower-level recipe is shared across the regional steps, so dependencies between its regions are retained.
-- source:
--   Regional tolerance-window step families and joint logarithmic regional recipes.

import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
import Theorems.Thm_mme_regional_tolerance_window_step_family

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.RecursiveYZ.CWCells
set_option autoImplicit false

theorem mme_joint_regional_tolerance_window_log_recipe_descent
    {N ell upper parts : ℕ} {P Q : Predicate N}
    (hlevel : ell < upper) (size : Fin parts → ℕ)
    (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (base : ∀ j, Predicate (size j)) (D : ∀ j, IntegerStep ell (size j) (base j))
    (delta eps rate : Fin parts → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j) (heps : ∀ j, 0 < eps j) (hrate : ∀ j, 0 ≤ rate j)
    (hsize : ∀ j, (8 * (D j).repairScale : ℝ) *
      (25 * (D j).R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        ((D j).minimum : ℝ) * (eps j)^2)
    (hbudget : ∀ j (mu : WindowProfile (D j)), WindowAdmissible (D j) mu →
      (∀ i, WindowClose (D j) (delta j) i (mu i)) →
        rate j ≤ windowLogBudget (D j) mu (eps j))
    (source : ∀ i x, (∀ j, parentWindow (D j) (eps j + 2 * delta j) i
      (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
    (target : ∀ i x, Q i x → ∀ j, childWindow (D j) (delta j) i
      (fun r ↦ x (positions ⟨j,r⟩)))
    (next : LogJointRecipe N ell Q) :
    ∃ E : LogJointRecipe N upper P,
      E.inputs ≤ (∏ j, (Fintype.card (Position (D j).n) + 1) ^
        (3 * Fintype.card (Cell (D j).half (D j).R (D j).parent) *
          Fintype.card (CompleteWord ell))) * next.inputs ∧
      E.logOutputs = (∑ j, rate j) + next.logOutputs ∧ E.dims = next.dims := by sorry
