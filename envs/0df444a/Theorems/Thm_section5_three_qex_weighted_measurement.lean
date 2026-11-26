-- Prove2me | Theorems.Thm_section5_three_qex_weighted_measurement
-- name    : section5_three_qex_weighted_measurement
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:36.185407+00:00
-- url     : https://prove2.me/theorems/489983bb-0e08-5fbe-97c3-6dd5e687182a
-- title:
--   Exact weighted measurement identity for three QEX states
-- statement:
--   Let w∈R^n, q natural, G any real function on triples of labelled example strings, p the finite Gaussian spatial law and L_w append the true negative-label bit. For Ψ=QEX_w⊗QEX_w⊗QEX_w, $$\sum_z|\Psi(z)|^2G(z)=\sum_{x_1,x_2,x_3}\left(\prod_{r=1}^3p(x_r)\right)G(L_w(x_1),L_w(x_2),L_w(x_3)).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ThreeQEXMeasurement.lean, lines 28–31.

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
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
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
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_qex_weighted_measurement
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_three_qex_weighted_measurement {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (G : Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1) → ℝ) :
    (∑ z, prob (section5_three_qex_state (q:=q) w) z*G z)=
      ∑ x, section5_three_qex_weight n q x*G (section5_labelled_three_qex_outcome w x) := by sorry
