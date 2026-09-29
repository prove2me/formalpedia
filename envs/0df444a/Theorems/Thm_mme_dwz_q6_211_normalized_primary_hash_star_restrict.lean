-- Prove2me | Theorems.Thm_mme_dwz_q6_211_normalized_primary_hash_star_restrict
-- name    : mme_dwz_q6_211_normalized_primary_hash_star_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:32:29.41799+00:00
-- url     : https://prove2.me/theorems/81bae0b3-e367-426b-a4a4-00a006e2579f
-- title:
--   The cyclically normalized q=6 row-211 source realizes the ordinary primary-family stars
-- statement:
--   After undoing the canonical row-211 router's once-cyclic output orientation, the twice-cyclic normalization of the literal restricted row realizes the unpermuted direct sum of every C-tensor star retained by an ordinary primary hash family.
-- source:
--   DWZ q=6 row-211 cyclic source normalization and primary-family star restriction.

import Theorems.Thm_mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
import Definitions.Def_mme_permutation
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_dwz_q6_211_normalized_primary_hash_star_restrict
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (starObj (dwzQ6CoupledGrading K) family))
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (restrictedComponentPower K (14 : Fin 15) m)) := by
  sorry
