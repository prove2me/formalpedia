-- Prove2me | Theorems.Thm_mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
-- name    : mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:29:36.927452+00:00
-- url     : https://prove2.me/theorems/d38ecdbf-a2e6-41a8-9bf8-67740dac3eee
-- title:
--   The restricted q=6 row-211 source realizes the once-cyclic primary-family stars
-- statement:
--   For every ordinary q=6 primary hash family with half-length $1036722900000000m$, the literal allowed-word projection of Table-2 row 211 restricts to the once-cyclic mode permutation of the direct sum of its retained C-tensor stars. This is the source-faithful projector descent needed before undoing the row router's cyclic orientation.
-- source:
--   DWZ q=6 Table-2 row 211; canonical powered source router, primary-family outer extraction, and allowed-word projection.

import Theorems.Thm_mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
import Theorems.Thm_mme_primary_hash_family_permuted_outer_extraction_exact
import Theorems.Thm_mme_perm_kronPow_mode_equiv_recursive_basis
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support
import Theorems.Thm_mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.permObj cyclicPerm
        (TensorObj.bigAdd
          (starObj (dwzQ6CoupledGrading K) family)))
      (restrictedComponentPower K (14 : Fin 15) m) := by
  sorry
