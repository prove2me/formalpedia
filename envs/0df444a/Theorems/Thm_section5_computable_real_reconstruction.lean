-- Prove2me | Theorems.Thm_section5_computable_real_reconstruction
-- name    : section5_computable_real_reconstruction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:38.444254+00:00
-- url     : https://prove2.me/theorems/0fc0e938-9589-4580-8328-68acacc8e89f
-- title:
--   Conditional computable rational direction recovery
-- statement:
--   Let n≥1, A a rational complex matrix whose operator L is self-adjoint, 0<ε<1 and 2^(k+1)≥400n/ε. Let w∈R^n be unit with ‖L−ww*‖≤ε/1000. Form r from the larger real or imaginary part of the maximum squared-norm column of the exact rational power A^(k+1). Then $$r\ne0,\qquad\min\{\|r/\|r\|-w\|,\|r/\|r\|+w\|\}\le\varepsilon/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RationalReconstruction.lean, lines 199–207.

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_power_column_estimator
import Theorems.Thm_section5_rational_best_column_correct
import Theorems.Thm_section5_rational_power_operator
import Theorems.Thm_section5_rational_real_candidate
import Theorems.Thm_section5_unnormalized_real_recovery
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_computable_real_reconstruction {n : ℕ} (hn : 1 ≤ n)
    (A : Section5RationalMatrix n) (hA : IsSelfAdjoint A.operator)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖A.operator-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/1000) :
    let r : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidate hn i:ℝ))
    r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by sorry
