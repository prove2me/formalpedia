-- Prove2me | Theorems.Thm_mme_entropy_regional_scalar_step_sharp_boundary_volume
-- name    : mme_entropy_regional_scalar_step_sharp_boundary_volume
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T06:47:24.670191+00:00
-- url     : https://prove2.me/theorems/c15a98c1-bf73-45fc-91a4-7a1ec49ce391
-- title:
--   A regional step with maximum boundary volume one
-- statement:
--   There is a valid level-one integer regional step on two elementary CW positions, inside the unrestricted source predicate, which admits a boundary block of volume one and for which every boundary block has volume at most one. Thus the hypotheses on an arbitrary integer step do not guarantee a boundary block of volume 25. The witness uses parent shape $(4,0,0)$ and half-split $(2,0,0)$; each output mode has a single allowed coordinate.
-- source:
--   Direct formal construction and dimension argument for the existing integer regional CW definitions; companion to the counterexample to mme_entropy_regional_boundary_match.

import Definitions.Def_mme_entropy_regional_CW_recipe
set_option autoImplicit false

theorem mme_entropy_regional_scalar_step_sharp_boundary_volume : ∃ S : MME.RegionRealization.IntegerStep 1 2 (fun _ _ ↦ True),
    (∃ B : MME.ProfiledCW.BoundaryEnd 1 2 S.output, B.a * B.b * B.c = 1) ∧
    ∀ B : MME.ProfiledCW.BoundaryEnd 1 2 S.output, B.a * B.b * B.c ≤ 1 := by sorry
