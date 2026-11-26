-- Prove2me | Theorems.Thm_section5_integer_scaled_candidate
-- name    : section5_integer_scaled_candidate
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:45.037889+00:00
-- url     : https://prove2.me/theorems/95a2172e-6ed2-5ea3-8151-813c267d36cf
-- title:
--   Integer candidate agrees with a scaled real powered column
-- statement:
--   Let A be a complex integer n×n matrix, q,t natural and j a column index. Let c_j be the larger squared-norm real or imaginary column of A^t, and R(y) the larger-norm real or imaginary part of a complex vector y, with ties choosing the real part. For L=2^(−q)op(A), $$2^{-(q+1)t}c_j=2^{-t}R(L^te_j).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerSpectralBridge.lean, lines 183–188.

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
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_integer_power_operator
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_integer_scaled_candidate {n : ℕ} (A : Section5IntegerMatrix n)
    (q t : ℕ) (j : Fin n) :
    ((2:ℝ)^((q+1)*t))⁻¹ •
        (WithLp.toLp 2 (fun i => ((A.power t).realCandidateAt j i:ℝ)))=
      ((2:ℝ)^t)⁻¹ • section5_larger_real_part
        ((A.dyadicOperator q^t) (section5_coordinate_ket j)) := by sorry
