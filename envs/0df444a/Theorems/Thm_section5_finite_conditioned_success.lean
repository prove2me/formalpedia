-- Prove2me | Theorems.Thm_section5_finite_conditioned_success
-- name    : section5_finite_conditioned_success
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:46.828522+00:00
-- url     : https://prove2.me/theorems/9e147709-ff92-451d-837c-007c6aec5704
-- title:
--   Product-weight success from conditional lower bounds
-- statement:
--   Let $T,Z$ be finite types and let $p_t,q_z$ be nonnegative real weights. Let $G\subseteq T$ and let $A\subseteq T\times Z$. Suppose $c\ge0$, $\sum_{t\in G}p_t\ge g$, and $\sum_{z:(t,z)\in A}q_z\ge c$ for each $t\in G$. Then
--
--   $$
--   \sum_{(t,z)\in A}p_tq_z\ge cg.
--   $$
--
--   No normalization of the weights is required; this combines a good-parameter mass bound with conditional success bounds.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5RawOrientation.lean, section5_finite_conditioned_success, lines 61–89.

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
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Example

theorem section5_finite_conditioned_success {T Z : Type*} [Fintype T] [Fintype Z]
    (p : T → ℝ) (q : Z → ℝ) (hp : ∀ t, 0 ≤ p t) (hq : ∀ z, 0 ≤ q z)
    (G : T → Prop) (A : T → Z → Prop) [DecidablePred G] [∀ t, DecidablePred (A t)]
    (c g : ℝ) (hc : 0 ≤ c)
    (hgood : (∑ t,if G t then p t else 0) ≥ g)
    (hconditional : ∀ t, G t → (∑ z,if A t z then q z else 0) ≥ c) :
    (∑ t,∑ z,if A t z then p t*q z else 0) ≥ c*g := by sorry
