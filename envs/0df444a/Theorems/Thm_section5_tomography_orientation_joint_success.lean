-- Prove2me | Theorems.Thm_section5_tomography_orientation_joint_success
-- name    : section5_tomography_orientation_joint_success
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T21:04:06.171359+00:00
-- url     : https://prove2.me/theorems/8daa40ac-e24d-5ecf-9a7a-ea7767d71382
-- title:
--   Conditional joint tomography and orientation success
-- statement:
--   Let n≥1, 2^q≥2^40n², w be real unit and 0<ε<1. Let a finite estimator t have probabilities p_t≥0 summing to one and unit directions u_t. Suppose mass at least 11/12 satisfies min{‖u_t−w‖,‖u_t+w‖}≤ε/6. With three independent Gaussian grid orientation examples, $$\Pr[\|\operatorname{oriented}(w,u_t,Z)-w\|\le\varepsilon]\ge73/96.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OrientationDecision.lean, lines 86–95. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Mathlib
import Theorems.Thm_section5_quantized_orientation_success
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

open Classical in
theorem section5_tomography_orientation_joint_success {T : Type*} [Fintype T]
    (n q : ℕ) (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (u : T → EuclideanSpace ℝ (Fin n)) (hu : ∀ t, ‖u t‖=1)
    (p : T → ℝ) (hp : ∀ t, 0 ≤ p t) (hpsum : ∑ t,p t=1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hgood : (∑ t : T, if ∃ flip : Bool, ‖(if flip then -(u t) else u t)-w‖ ≤ ε/6 then p t else 0) ≥ 11/12) :
    (∑ t : T, ∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if ‖section5_oriented_direction w (u t) z-w‖ ≤ ε then
        p t*section5_three_qex_weight n q z else 0) ≥ 73/96 := by sorry
