-- Prove2me | Theorems.Thm_section5_mixed_three_qex_probability
-- name    : section5_mixed_three_qex_probability
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:33.232877+00:00
-- url     : https://prove2.me/theorems/f562f26a-a5eb-49a1-a6b2-55237eeacd48
-- title:
--   Mixed-data event law for three QEX states
-- statement:
--   Let E identify a finite basis I with α times three labelled example spaces, σ any complex α×α matrix, w∈R^n, and U implement a basis permutation F. Form the reindexed density matrix ρ from σ tensored with the three-QEX pure density. For a decidable event P, $$\operatorname{probMixed}(U,\rho,P)=\sum_{d,x_1,x_2,x_3}\mathbf1_{P(F(E^{-1}(d,L_w(x_1),L_w(x_2),L_w(x_3))))}\operatorname{Re}\sigma_{dd}\prod_{r=1}^3p(x_r).$$ Here p is the finite Gaussian spatial law and L_w appends the true negative-label bit; no positivity or trace hypothesis is required for this identity.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5MixedQEXMeasurement.lean, lines 28–37.

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
import Definitions.Def_Section5Verified_Section5MixedQEXMeasurement
import Definitions.Def_Section5Verified_Section5OrientationDecision
import Definitions.Def_Section5Verified_Section5ThreeQEXMeasurement
import Mathlib
import Theorems.Thm_section5_basis_permutation_conjugation
import Theorems.Thm_section5_three_qex_weighted_measurement
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement QuantumLTF.Example
open scoped ComplexConjugate

theorem section5_mixed_three_qex_probability {ι α : Type} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] {n q : ℕ}
    (E : ι ≃ α × (Qubits (n*q+1) × Qubits (n*q+1) × Qubits (n*q+1)))
    (σ : Matrix α α ℂ) (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix ι ι ℂ) (F : Equiv.Perm ι) (hact : ∀ z, act U (ket z)=ket (F z))
    (P : ι → Prop) [DecidablePred P] :
    probMixed U (section5_mixed_qex_density E σ w) P=
      ∑ d : α, ∑ x : Qubits (n*q) × Qubits (n*q) × Qubits (n*q),
        if P (F (E.symm (d,section5_labelled_three_qex_outcome w x))) then
          (σ d d).re*section5_three_qex_weight n q x else 0 := by sorry
