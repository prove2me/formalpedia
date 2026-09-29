-- Prove2me | solution 1 for mme_dwz_q6_canonical_220_table2_component_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:20:15.746315+00:00
-- url     : https://prove2.me/submissions/b208b500-b92c-4a70-9c93-85a5534f9a9c

import Mathlib.Tactic
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_CW_square_canonical_central220_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_MMObj_one_middle_one_tau_value

open MME MME.DWZSquare

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType 2 2 0))
      tau (componentBase tau (11 : Fin 15)) := by
  have hMM :
      HasTauValueAtLeast (MMObj K 1 38 1) tau (Real.rpow 38 tau) :=
    mme_MMObj_one_middle_one_tau_value (K := K) 38 tau
  have hrestrict : TensorObj.Restrict (MMObj K 1 38 1)
      ((cwSquareCanonicalGrading K 6).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by
    simpa using mme_CW_square_canonical_central220_restrict (K := K) 6
  have hblock := mme_HasTauValueAtLeast_mono_restrict hrestrict hMM
  simpa [componentBase] using hblock
