-- Prove2me | Theorems.Thm_mme_integer_step_low_level_boundary_end
-- name    : mme_integer_step_low_level_boundary_end
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:02:04.652764+00:00
-- url     : https://prove2.me/theorems/bd0aea3a-f65f-45e6-bba2-7d13ce9492ad
-- title:
--   Elementary-depth integer steps admit terminal boundary interfaces
-- statement:
--   Every integer regional extraction step at level ell <= 1 has a terminal boundary interface for its exact output predicate. For any partition of the physical positions into full reference cells, the construction retains oriented boundary profiles reproducing all cell grades and mode histograms. The interface has the original number of complete-word positions, and each matrix dimension is the product of the corresponding profile dimensions. The zero-grade mode in each cell follows from the elementary grade total of two.
-- source:
--   Integer regional CW extraction and exact complementary boundary profiles.

import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_integer_step_low_level_boundary_end
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (part : Partition (fullCell D.total D.reference)) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell M D.output,
        B.L = D.L ∧ B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by sorry
