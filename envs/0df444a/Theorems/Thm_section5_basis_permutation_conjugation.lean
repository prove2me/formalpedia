-- Prove2me | Theorems.Thm_section5_basis_permutation_conjugation
-- name    : section5_basis_permutation_conjugation
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:41:40.178256+00:00
-- url     : https://prove2.me/theorems/cadd23b6-71d4-459e-a24d-fa83c373156f
-- title:
--   Density-matrix conjugation by a basis permutation
-- statement:
--   Let the basis index set I be finite, U and ρ complex I×I matrices, and F a permutation with U|x⟩=|F(x)⟩ for all x. Then every pair of matrix entries satisfies $$ (U\rho U^*)_{F(x),F(y)}=\rho_{x,y}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ClassicalMeasurementLaw.lean, lines 12–15.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_probMixed
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem section5_basis_permutation_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U ρ : Matrix ι ι ℂ) (f : Equiv.Perm ι)
    (hact : ∀ x, act U (ket x)=ket (f x)) (x y : ι) :
    (U*ρ*U.conjTranspose) (f x) (f y)=ρ x y := by sorry
