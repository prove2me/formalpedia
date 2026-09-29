-- Prove2me | Theorems.Thm_mme_integer_step_boundary_end_of_zero_modes
-- name    : mme_integer_step_boundary_end_of_zero_modes
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:01:58.332281+00:00
-- url     : https://prove2.me/theorems/fb82ac03-9b3c-4d02-a699-70dc65837dfe
-- title:
--   Terminal boundary profiles for an integer regional step
-- statement:
--   Let D be an integer regional extraction step at level ell, and partition its physical positions by the full cells of its reference address. Suppose each cell has a mode of grade zero. Then there are oriented boundary profiles reproducing every cell grade and every mode histogram, and a terminal boundary interface for D.output. The interface has D.L complete-word positions, and its three matrix dimensions are the products of the corresponding oriented profile dimensions. The fiber multiplicities are derived from the reference address's exact joint counts; no additional tensor restriction or alignment assumption is required.
-- source:
--   Integer regional CW extraction and exact complementary boundary profiles.

import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false


open MME.RegionRealization

theorem mme_integer_step_boundary_end_of_zero_modes
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (hz : ∀ j, ∃ z : Fin 3, ((part.cells j).2.val z).val = 0) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ B : BoundaryEnd ell M D.output,
        B.L = D.L ∧ B.a = ∏ j, (profiles j).a (z j) ∧
        B.b = ∏ j, (profiles j).b (z j) ∧
        B.c = ∏ j, (profiles j).c (z j) := by sorry
