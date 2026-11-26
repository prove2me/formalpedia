-- Prove2me | Theorems.Thm_section5_quantized_tomography_reconstruction
-- name    : section5_quantized_tomography_reconstruction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:48.729827+00:00
-- url     : https://prove2.me/theorems/47b3f744-3fc2-50e8-92cb-0953a0466839
-- title:
--   Conditional quantized spectral direction recovery
-- statement:
--   Let n≥1 and L be self-adjoint on C^n. There exists a unit v such that, for real unit w, 0<ε<1 and 2^f≥128n/ε, the hypothesis ‖L−ww*‖≤ε/192 implies the following. Let r be the f-bit dyadic quantization of the larger-norm real or imaginary part of v. Then $$r\ne0,\qquad\min\{\|r/\|r\|-w\|,\|r/\|r\|+w\|\}\le\varepsilon/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5QuantizedReconstruction.lean, lines 28–36.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5FixedPointQuantization
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_quantize_normalized_error
import Theorems.Thm_section5_real_direction_recovery
import Theorems.Thm_section5_spectral_estimator_exists
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_quantized_tomography_reconstruction (n : ℕ) (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖=1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ f : ℕ, 128*(n:ℝ)/ε ≤ (2:ℝ)^f →
      ‖L-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/192 →
        let r := section5_quantize_vector f (section5_larger_real_part v)
        r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by sorry
