-- Prove2me | Theorems.Thm_section5_reindexed_three_qex_probability
-- name    : section5_reindexed_three_qex_probability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:24.464856+00:00
-- url     : https://prove2.me/theorems/e528329c-9203-4b51-b43d-73255477f76f
-- title:
--   Three-QEX event law under a basis reindexing
-- statement:
--   Let E identify a finite basis I with α times three labelled example spaces. Let a∈α, w∈R^n and U represent a basis permutation F of I. For any decidable event P, the reindexed state Ψ corresponding to |a⟩⊗QEX_w^⊗3 satisfies $$\operatorname{probEvent}(U\Psi,P)=\sum_{x_1,x_2,x_3}\mathbf1_{P(F(E^{-1}(a,L_w(x_1),L_w(x_2),L_w(x_3))))}\prod_{r=1}^3p(x_r),$$ where p is the finite Gaussian spatial law and L_w appends the true negative-label bit.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ReindexedQEXLaw.lean, lines 24–33.

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
import Definitions.Def_Section5Verified_Section5ReindexedQEXLaw
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_basis_permutation_probEvent
import Theorems.Thm_section5_three_qex_weighted_measurement
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_reindexed_three_qex_probability {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (w : EuclideanSpace ℝ (Fin n)) (a : α)
    (U : Matrix ι ι ℂ) (F : Equiv.Perm ι) (hact : ∀ z, act U (ket z)=ket (F z))
    (P : ι → Prop) [DecidablePred P] :
    probEvent (act U (section5_reindex_state E
      (tensorVec (ket a) (section5_three_qex_state (q:=q) w)))) P=
      ∑ x, if P (F (E.symm (a,section5_labelled_three_qex_outcome w x))) then
        section5_three_qex_weight n q x else 0 := by sorry
