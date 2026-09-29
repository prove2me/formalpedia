-- Prove2me | Theorems.Thm_mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
-- name    : mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T12:56:03.87656+00:00
-- url     : https://prove2.me/theorems/7615dc77-6406-426d-848e-8669c9e5fcab
-- title:
--   Mode-one primary-family outer extraction kills a wrong-profile word
-- statement:
--   Let a primary hash family consist of exact coupled addresses of length $2N$, with the prescribed balanced marginal profile in the first two modes. If a recursive product-basis word in mode one has any grade multiplicity different from that profile, then the complete shared-third-mode outer extraction annihilates its basis vector:
--
--   $$
--   E_1(b_w)=0.
--   $$
--
--   Every summand of the outer extraction projects onto one retained component address, and all such addresses have the prescribed mode-one histogram. A wrong-profile word must disagree with each address somewhere, so its address projection vanishes. This is the exact slotwise zeroing interface needed for the normalized q=6 row-211 projector descent.
-- source:
--   Coppersmith--Winograd primary-family address projection mechanism for the coupled q=6 tensor; exact mode-one zeroing needed for the DWZ row-211 source restriction.

import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false

theorem mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
    {K : Type u} [Field K]
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) (2 * N))
    (hnot : ¬ ∀ a : Fin 3,
      (Finset.univ.filter (fun r : Fin (2 * N) ↦
        dwzQ6CoupledCoordGrade 1
          (PowIndex.get (2 * N) w r).down = a)).card =
        cwQ6CoupledMarginalMultiplicity N L G 1 a) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 1
        (kronPowModeBasis (coupledObj K 6) 1
          ((dwzQ6CoupledBasis K 1).reindex Equiv.ulift.symm)
          (2 * N) w) = 0 := by
  sorry
