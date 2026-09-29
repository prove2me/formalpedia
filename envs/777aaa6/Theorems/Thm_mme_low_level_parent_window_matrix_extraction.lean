-- Prove2me | Theorems.Thm_mme_low_level_parent_window_matrix_extraction
-- name    : mme_low_level_parent_window_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:19:23.241681+00:00
-- url     : https://prove2.me/theorems/82fdd59f-0474-4ef7-87d8-4528ae4b41d0
-- title:
--   Matrix extraction from an elementary parent tolerance window
-- statement:
--   Let $K$ be a field and let $D$ be an integer regional extraction step at depth $\ell\le1$. Choose $0<\varepsilon\le\eta$ satisfying the scalar size test, and a nonnegative rate $r$ below the central profile's explicit logarithmic copy budget at tolerance $\varepsilon$. Then there are oriented boundary profiles reproducing every physical cell grade and mode histogram, and an integer $k$ with
--   \[
--   e^r\le k,
--   \]
--   such that a direct sum of $k$ identical matrix multiplication tensors restricts from one copy of the parent-window tensor of radius $\eta$. Each of the three matrix dimensions is the product of the corresponding oriented boundary-profile dimensions. The source is the actual projected CW tensor defined by the parent tolerance predicate; the result does not assume a tensor restriction or a terminal boundary interface.
-- source:
--   Elementary parent-window recipes and the verified regional tensor compilation chain.

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

theorem mme_low_level_parent_window_matrix_extraction
    {K : Type u} [Field K] {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) (hlevel : ell ≤ 1)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ k : ℕ, Real.exp rate ≤ (k : ℝ) ∧
        Restrict (bigAdd (fun _ : Fin k ↦ MMObj K
          (∏ j, (profiles j).a (z j)) (∏ j, (profiles j).b (z j))
          (∏ j, (profiles j).c (z j))))
          (bigAdd (fun _ : Fin 1 ↦ tensor K (parentWindow D eta))) := by sorry
