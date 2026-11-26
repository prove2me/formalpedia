-- Prove2me | Theorems.Thm_section5_quantized_orientation_success
-- name    : section5_quantized_orientation_success
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:59:26.917109+00:00
-- url     : https://prove2.me/theorems/94502232-4f4b-5289-962a-11bf5e46f063
-- title:
--   Conditional success of quantized orientation
-- statement:
--   Let n≥1, 2^q≥2^40n², w,u be real unit vectors, 0<ε<1, and b a Boolean sign with ‖(−1)^b u−w‖≤ε/6. For three independent Gaussian grid examples, the majority-oriented output R satisfies $$\Pr[\|R-w\|\le\varepsilon]\ge27/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OrientationDecision.lean, lines 53–59. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5OrientationAmplification
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5QuantizedOrientation
import Mathlib
import Theorems.Thm_section5_majority_decision_correct
import Theorems.Thm_section5_three_quantized_orientation_error
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

open Classical in
theorem section5_quantized_orientation_success (n q : ℕ) (hn : 1 ≤ n)
    (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w u : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1) (hu : ‖u‖=1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (flip : Bool) (hclose : ‖(if flip then -u else u)-w‖ ≤ ε/6) :
    (∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if ‖section5_oriented_direction w u z-w‖ ≤ ε then section5_three_qex_weight n q z else 0) ≥ 27/32 := by sorry
