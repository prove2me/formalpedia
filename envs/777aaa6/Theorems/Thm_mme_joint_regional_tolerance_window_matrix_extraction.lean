-- Prove2me | Theorems.Thm_mme_joint_regional_tolerance_window_matrix_extraction
-- name    : mme_joint_regional_tolerance_window_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:41:31.203094+00:00
-- url     : https://prove2.me/theorems/8865d639-aca4-4611-9f9b-0e46c55108be
-- title:
--   Matrix extraction from simultaneous regional tolerance windows
-- statement:
--   Let $K$ be a field. Partition the coordinate positions into regions equipped with integer extraction steps, nonnegative child tolerances $\delta_j$, positive parent tolerances $\varepsilon_j$, and nonnegative rates $r_j$. Assume the scalar size tests and uniform admissible-profile window budgets. Suppose the regional parent windows of radii $\varepsilon_j+2\delta_j$ lie in the source predicate $P$, and a shared lower-level joint recipe $F$ has its predicate inside all regional child windows. Write $H_j=(|\operatorname{Position}_j|+1)^{3|\operatorname{Cell}_j||\operatorname{CompleteWord}_{\ell}|}$. There are natural numbers $s,k$ with
--   \[
--   s\le\Bigl(\prod_j H_j\Bigr)\operatorname{inputs}(F),\qquad
--   k\ge\exp\!\left(\sum_j r_j+\operatorname{logOutputs}(F)\right),
--   \]
--   such that $k$ copies of the matrix multiplication tensor with dimensions $(F.a,F.b,F.c)$ restrict from $s$ copies of the tensor defined by $P$. The regional rates combine before compiling the shared next recipe.
-- source:
--   Regional tolerance-window step families and joint logarithmic regional recipes.

import Theorems.Thm_mme_logarithmic_joint_regional_recipe_compilation
import Theorems.Thm_mme_joint_regional_CW_plan_sound
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
import Theorems.Thm_mme_regional_tolerance_window_step_family

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.RecursiveYZ.CWCells
open MME.TensorObj
set_option autoImplicit false


universe u

theorem mme_joint_regional_tolerance_window_matrix_extraction
    {K : Type u} [Field K] {N ell upper parts : ℕ} {P Q : Predicate N}
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
    ∃ inputs copies : ℕ,
      inputs ≤ (∏ j, (Fintype.card (Position (D j).n) + 1) ^
        (3 * Fintype.card (Cell (D j).half (D j).R (D j).parent) *
          Fintype.card (CompleteWord ell))) * next.inputs ∧
      Real.exp ((∑ j, rate j) + next.logOutputs) ≤ (copies : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin copies ↦ MMObj K next.a next.b next.c))
        (bigAdd (fun _ : Fin inputs ↦ tensor K P)) := by sorry
