-- Prove2me | Theorems.Thm_mme_low_level_parent_window_explicit_matrix_extraction
-- name    : mme_low_level_parent_window_explicit_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:27:13.814239+00:00
-- url     : https://prove2.me/theorems/9cded2d3-14f5-4fac-9b3c-94b67ee7fbe4
-- title:
--   Parent-window matrix extraction with explicit physical dimensions
-- statement:
--   Let $K$ be a field and $D$ an integer regional extraction step at depth $\ell\le1$. Choose $0<\varepsilon\le\eta$ satisfying the step's scalar size test, and a nonnegative rate $r$ below the explicit central-profile logarithmic copy budget at tolerance $\varepsilon$. Partition the physical reference cells as $j$, with multiplicities $L_j$ and grades $g_{j,0},g_{j,1},g_{j,2}$. Define
--   \[
--   A=\sum_j L_j\mathbf1[g_{j,1}=0,\ g_{j,0}=1],\quad
--   B=\sum_j L_j\mathbf1[g_{j,2}=0,\ g_{j,0}=1],\quad
--   C=\sum_j L_j\mathbf1[g_{j,0}=0,\ g_{j,1}=1].
--   \]
--   There is an integer $k\ge e^r$ such that a direct sum of $k$ copies of the matrix multiplication tensor $\langle5^A,5^B,5^C\rangle$ restricts from one copy of the parent-window tensor of radius $\eta$. The dimensions depend explicitly on the physical cell counts, without existential boundary-profile parameters.
-- source:
--   Elementary exact boundary profiles and the regional parent-window matrix extraction.

import Theorems.Thm_mme_logarithmic_regional_recipe_compilation
import Theorems.Thm_mme_entropy_regional_recipe_compilation
import Theorems.Thm_mme_integer_regional_recipe_compilation
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Definitions.Def_mme_logarithmic_regional_CW_recipe
import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization MME.TensorObj
universe u

theorem mme_low_level_parent_window_explicit_matrix_extraction
    {K : Type u} [Field K] {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) (hlevel : ell ≤ 1)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ k : ℕ, Real.exp rate ≤ (k : ℝ) ∧
      Restrict (bigAdd (fun _ : Fin k ↦ MMObj K
        (5 ^ (∑ j, if ((part.cells j).2.val 1).val = 0 ∧
          ((part.cells j).2.val 0).val = 1 then part.size j else 0))
        (5 ^ (∑ j, if ((part.cells j).2.val 2).val = 0 ∧
          ((part.cells j).2.val 0).val = 1 then part.size j else 0))
        (5 ^ (∑ j, if ((part.cells j).2.val 0).val = 0 ∧
          ((part.cells j).2.val 1).val = 1 then part.size j else 0))))
        (bigAdd (fun _ : Fin 1 ↦ tensor K (parentWindow D eta))) := by sorry
