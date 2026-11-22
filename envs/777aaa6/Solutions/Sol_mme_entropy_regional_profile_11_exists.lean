-- Prove2me | solution 1 for mme_entropy_regional_profile_11_exists
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T19:51:43.239436+00:00
-- url     : https://prove2.me/submissions/76b72e92-07b4-47a3-a173-54f5ecbb5bc7

import Definitions.Def_mme_recursive_yz_boundary_data
import Mathlib.Tactic

set_option autoImplicit false

theorem solution :
    exists (prof : MME.RecursiveYZ.Boundary.Profile 2 1), prof.dim = 25 := by
  refine ⟨⟨2, by decide,
    (fun s => if s = (fun _ => (1 : Fin 3)) then 1 else 0),
    by decide, by decide⟩, by decide⟩
