-- Prove2me | Theorems.Thm_mme_low_level_parent_window_count_matrix_extraction
-- name    : mme_low_level_parent_window_count_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:31:34.523955+00:00
-- url     : https://prove2.me/theorems/c8bd0988-a550-4703-b3db-f5a4d51aa748
-- title:
--   Elementary parent-window matrix extraction from prescribed counts
-- statement:
--   Let K be a field and D an integer regional step at depth at most one. Choose positive tolerances eps <= eta satisfying the scalar size test and a nonnegative rate below the central-profile window budget at eps. Set A to the sum of m(r,c)+m(r,complement(c)) over cells of grades g1=0,g0=1; define B with g2=0,g0=1 and C with g0=0,g1=1. Then for some integer k >= exp(rate), a direct sum of k copies of the matrix multiplication tensor with dimensions (5^A,5^B,5^C) restricts from one copy of the parent-window tensor of radius eta. All dimension exponents are expressed in the prescribed integer counts, without choosing a physical cell enumeration.
-- source:
--   Physical cell fibers and elementary regional parent-window extraction.

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

theorem mme_low_level_parent_window_count_matrix_extraction
    {K : Type u} [Field K] {ell M : ℕ} {P : Predicate M}
    (D : IntegerStep ell M P) (hlevel : ell ≤ 1)
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ k : ℕ, Real.exp rate ≤ (k : ℝ) ∧
      Restrict (bigAdd (fun _ : Fin k ↦ MMObj K
        (5 ^ (∑ r, ∑ c, if (c.val 1).val = 0 ∧ (c.val 0).val = 1 then
          D.m r c + D.m r (complement (D.total r) c) else 0))
        (5 ^ (∑ r, ∑ c, if (c.val 2).val = 0 ∧ (c.val 0).val = 1 then
          D.m r c + D.m r (complement (D.total r) c) else 0))
        (5 ^ (∑ r, ∑ c, if (c.val 0).val = 0 ∧ (c.val 1).val = 1 then
          D.m r c + D.m r (complement (D.total r) c) else 0))))
        (bigAdd (fun _ : Fin 1 ↦ tensor K (parentWindow D eta)))  := by sorry
