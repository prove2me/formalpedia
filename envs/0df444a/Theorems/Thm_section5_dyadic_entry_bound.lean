-- Prove2me | Theorems.Thm_section5_dyadic_entry_bound
-- name    : section5_dyadic_entry_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:02.6931+00:00
-- url     : https://prove2.me/theorems/4543cdf1-b775-5645-81c6-258a574d8f2a
-- title:
--   Integer entry bounds from dyadic operator proximity
-- statement:
--   Let A be a complex integer n×n matrix, q natural and w∈C^n unit. If ‖2^(−q)op(A)−ww*‖≤1, then each real and imaginary component is bounded by $$|\operatorname{Re}A_{ij}|\le2^{q+1},\qquad|\operatorname{Im}A_{ij}|\le2^{q+1}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5IntegerSpectralBridge.lean, lines 107–110.

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
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_dyadic_entry_bound {n : ℕ} (A : Section5IntegerMatrix n) (q : ℕ)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖A.dyadicOperator q-rankOne ℂ w w‖ ≤ 1) :
    A.Bounded ((2:ℤ)^(q+1)) := by sorry
