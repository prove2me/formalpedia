-- Prove2me | Theorems.Thm_section5_scaled_integer_candidate_bounds
-- name    : section5_scaled_integer_candidate_bounds
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:17:56.211589+00:00
-- url     : https://prove2.me/theorems/fa0a72cf-f681-4d54-8282-ceee17125363
-- title:
--   Bounds on a scaled selected integer candidate
-- statement:
--   Let n≥1, A a complex integer matrix and L=2^(−q)op(A) self-adjoint. Suppose w is real unit, 0≤η≤1/1000 and ‖L−ww*‖≤η. For j maximizing the column score of A^(k+1), let r be its larger real or imaginary column scaled by 2^(−(q+1)(k+1)). Then $$\frac1{3n4^{k+1}}\le\|r\|\le1.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5DyadicDecoderGuarantee.lean, lines 12–20.

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_dyadic_max_score_column
import Theorems.Thm_section5_integer_scaled_candidate
import Theorems.Thm_section5_power_column_magnitude_bounds
import Theorems.Thm_section5_scaled_power_output_bounds
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives ContinuousLinearMap InnerProductSpace

theorem section5_scaled_integer_candidate_bounds {n : ℕ} (hn : 1 ≤ n)
    (A : Section5IntegerMatrix n) (q k : ℕ) (hA : IsSelfAdjoint (A.dyadicOperator q))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/1000)
    (herror : ‖A.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ η)
    (j : Fin n) (hmax : ∀ i, (A.power (k+1)).columnScore i ≤ (A.power (k+1)).columnScore j) :
    let r := ((2:ℝ)^((q+1)*(k+1)))⁻¹ •
      (WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidateAt j i:ℝ)))
    1/(3*n*(4:ℝ)^(k+1)) ≤ ‖r‖ ∧ ‖r‖ ≤ 1 := by sorry
