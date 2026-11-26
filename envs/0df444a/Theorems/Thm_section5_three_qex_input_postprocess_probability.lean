-- Prove2me | Theorems.Thm_section5_three_qex_input_postprocess_probability
-- name    : section5_three_qex_input_postprocess_probability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:48.681186+00:00
-- url     : https://prove2.me/theorems/7b7ad6b1-6272-55ce-8aa6-b6b0c9ded576
-- title:
--   Three-QEX measurement with a classical basis input
-- statement:
--   Let α be a finite basis set, a∈α, w∈R^n and U a basis-permutation matrix representing F on α times three labelled example spaces. For a decidable event P, let L_w append the true negative labels and p denote normalized Gaussian grid weights. Then $$\operatorname{probEvent}(U(|a\rangle\otimes\operatorname{QEX}_w^{\otimes3}),P)=\sum_{x_1,x_2,x_3}\mathbf1_{P(F(a,L_w(x_1),L_w(x_2),L_w(x_3)))}\prod_{r=1}^3p(x_r).$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5OrientationBornSuccess.lean, lines 23–32.

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
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_basis_permutation_probEvent
import Theorems.Thm_section5_three_qex_weighted_measurement
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_three_qex_input_postprocess_probability {α : Type*} [Fintype α] [DecidableEq α]
    {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) (a : α)
    (U : Matrix (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
      (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1))) ℂ)
    (F : Equiv.Perm (α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1))))
    (hact : ∀ z, act U (ket z)=ket (F z))
    (P : α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)) → Prop) [DecidablePred P] :
    probEvent (act U (tensorVec (ket a) (section5_three_qex_state (q:=q) w))) P=
      ∑ x, if P (F (a,section5_labelled_three_qex_outcome w x)) then
        section5_three_qex_weight n q x else 0 := by sorry
