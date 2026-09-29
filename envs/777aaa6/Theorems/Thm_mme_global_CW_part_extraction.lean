-- Prove2me | Theorems.Thm_mme_global_CW_part_extraction
-- name    : mme_global_CW_part_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:27:39.976577+00:00
-- url     : https://prove2.me/theorems/c4a876b0-d1e2-4fbe-9b31-23247d24676e
-- title:
--   Actual typed and oriented global CW extraction
-- statement:
--   An exact type cover with explicit finite global hash and copy budgets extracts a uniform number of copies of its full profile interface. Cyclic and transposition orientations are included by actual CW mode-permutation isomorphisms.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_joint_start_data
open MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_part_extraction {K : Type u} [Field K] {M ell : ℕ} {T : Predicate M}
    (D : GlobalCW.Part M ell T) :
    Restrict (bigAdd (fun _ : Fin ⌈Real.exp D.rate⌉₊ ↦ tensor K T))
      (bigAdd (fun _ : Fin D.inputs ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  sorry
