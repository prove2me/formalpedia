-- Prove2me | Theorems.Thm_section5_basis_permutation_probEvent
-- name    : section5_basis_permutation_probEvent
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:49.992835+00:00
-- url     : https://prove2.me/theorems/a1b7b8c2-7a3c-44fe-8a13-a3473c86e666
-- title:
--   Pure measurement law after a basis permutation
-- statement:
--   Let I be finite, F a basis permutation and U a complex matrix with U|x⟩=|F(x)⟩ for all x. For any complex vector ψ and decidable basis event P, $$\operatorname{probEvent}(U\psi,P)=\sum_x\mathbf1_{P(F(x))}|\psi_x|^2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ClassicalMeasurementLaw.lean, lines 45–49.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_basis_permutation_probEvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (ψ : EuclideanSpace ℂ ι)
    (P : ι → Prop) [DecidablePred P] :
    probEvent (act U ψ) P=∑ x : ι, if P (f x) then prob ψ x else 0 := by sorry
