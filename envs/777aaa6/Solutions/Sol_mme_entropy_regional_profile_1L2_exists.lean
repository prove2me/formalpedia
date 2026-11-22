-- Prove2me | solution 1 for mme_entropy_regional_profile_1L2_exists
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:11:57.709308+00:00
-- url     : https://prove2.me/submissions/0f7982cc-84e3-40cd-ac86-5fb96d812de0

import Definitions.Def_mme_recursive_yz_boundary_data
import Mathlib.Tactic

set_option autoImplicit false

theorem solution :
    exists (prof : MME.RecursiveYZ.Boundary.Profile 1 2), prof.dim = 25 := by
  refine ⟨⟨1, by decide,
    (fun s => if s = (fun _ => (1 : Fin 3)) then 2 else 0),
    by decide, by decide⟩, by decide⟩
