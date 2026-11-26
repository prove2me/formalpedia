-- Prove2me | Theorems.Thm_section5_raw_tomography_joint_success
-- name    : section5_raw_tomography_joint_success
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T21:09:59.889419+00:00
-- url     : https://prove2.me/theorems/39e2b5bb-9bca-4b43-8d5a-607f5a308493
-- title:
--   Conditional joint success for raw tomography outputs
-- statement:
--   Let n≥1, 2^q≥2^40n², w real unit and 0<ε<1. Let a finite family r_t∈R^n carry nonnegative weights p_t. Assume weight at least 11/12 lies on nonzero r_t whose normalized direction is within ε/6 of ±w. Independently apply three Gaussian grid orientation examples. The resulting weighted success obeys $$\sum_t p_t\Pr[R_t\ne0,\ \|R_t/\|R_t\|-w\|\le\varepsilon]\ge73/96.$$ Normalization of the p_t is not separately required.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5RawOrientation.lean, lines 92–103. The Gaussian-disagreement foundation is credited to kmehltretter82, accepted Prove2Me submission f5f65d6e-b702-475a-bc3e-8683c2844aa9 (Apache-2.0), copied in Solutions/Section5GaussianDisagreementFoundation.lean.

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
import Theorems.Thm_section5_finite_conditioned_success
import Theorems.Thm_section5_raw_orientation_success
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

open Classical in
theorem section5_raw_tomography_joint_success {T : Type*} [Fintype T]
    (n q : ℕ) (hn : 1 ≤ n) (hgrid : (2:ℝ)^40*(n:ℝ)^2 ≤ (2:ℝ)^q)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (r : T → EuclideanSpace ℝ (Fin n)) (p : T → ℝ) (hp : ∀ t, 0 ≤ p t)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hgood : (∑ t,if r t ≠ 0 ∧ ∃ flip : Bool,
        ‖(if flip then -NormedSpace.normalize (r t) else NormedSpace.normalize (r t))-w‖ ≤ ε/6
      then p t else 0) ≥ 11/12) :
    (∑ t,∑ z : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
      if section5_oriented_direction w (r t) z ≠ 0 ∧
          ‖NormedSpace.normalize (section5_oriented_direction w (r t) z)-w‖ ≤ ε then
        p t*section5_three_qex_weight n q z else 0) ≥ 73/96 := by sorry
