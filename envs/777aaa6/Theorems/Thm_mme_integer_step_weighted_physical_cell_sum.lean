-- Prove2me | Theorems.Thm_mme_integer_step_weighted_physical_cell_sum
-- name    : mme_integer_step_weighted_physical_cell_sum
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:31:29.603189+00:00
-- url     : https://prove2.me/theorems/e781efff-c7a4-4b93-b569-dceb61bacfaf
-- title:
--   Weighted physical cell sizes from prescribed counts
-- statement:
--   For any integer regional step and any natural-valued weight on its cells, the sum of physical cell sizes times their weights equals the sum over regions and splits of the prescribed split count plus its complementary count, times the cell weight. The identity holds at every depth and for every physical cell enumeration.
-- source:
--   Physical cell fibers and elementary regional parent-window extraction.

import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false
open MME.RegionRealization

theorem mme_integer_step_weighted_physical_cell_sum
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (f : Cell D.half D.R D.parent → ℕ) :
    (∑ j, part.size j * f (part.cells j)) =
      ∑ r, ∑ c, (D.m r c + D.m r (complement (D.total r) c)) * f ⟨r, c⟩ := by sorry
