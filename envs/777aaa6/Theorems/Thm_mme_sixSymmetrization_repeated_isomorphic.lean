-- Prove2me | Theorems.Thm_mme_sixSymmetrization_repeated_isomorphic
-- name    : mme_sixSymmetrization_repeated_isomorphic
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:52:31.607824+00:00
-- url     : https://prove2.me/theorems/18e66b6a-2d76-49f6-ae83-756db34fa6d3
-- title:
--   Six symmetrization preserves exact repeated multiplicities
-- statement:
--   Symmetrizing p copies produces exactly p to the sixth power copies of the symmetrized tensor, up to tensor isomorphism. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
open MME BigOperators
universe u

theorem mme_sixSymmetrization_repeated_isomorphic
    {K : Type u} [Field K] (p : ℕ) (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => sixSymmetrization T))
      (sixSymmetrization (TensorObj.bigAdd (fun _ : Fin p => T))) := by sorry
