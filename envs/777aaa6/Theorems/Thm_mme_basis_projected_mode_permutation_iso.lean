-- Prove2me | Theorems.Thm_mme_basis_projected_mode_permutation_iso
-- name    : mme_basis_projected_mode_permutation_iso
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T15:12:16.026627+00:00
-- url     : https://prove2.me/theorems/0cf1a042-fc73-4412-af41-fee43e6837e3
-- title:
--   Mode permutations commute with projections of a symmetric tensor
-- statement:
--   Let a three-mode tensor have mode bases indexed by the same finite set, with coefficients invariant under a permutation $\sigma$. For mode predicates $P_i$, the tensor projected by $P_{\sigma^{-1}(i)}$ is isomorphic to the mode permutation of the tensor projected by $P_i$.
--
--   $$T[P\circ\sigma^{-1}]\cong\sigma(T[P]).$$
--
--   This permits changing the asymmetric roles of an already projected tensor while preserving its exact profile constraints.
-- source:
--   Constructive tensor-algebra components for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 , Proposition 6.3 and Theorem 6.4. These lemmas implement the finite operations; they do not assert the numerical witness.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_permutation
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
open MME MME.TensorObj Module
universe u
set_option autoImplicit false

theorem mme_basis_projected_mode_permutation_iso {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Type u} [Fintype I] (b : ∀ i, Basis I K (T.V i))
    (sigma : Equiv.Perm (Fin 3)) (P : Fin 3 → I → Prop)
    (hsymmetric : ∀ x : Fin 3 → I,
      (Basis.piTensorProduct b).repr T.t (fun i ↦ x (sigma i)) =
        (Basis.piTensorProduct b).repr T.t x) :
    Isomorphic (T.basisAllAllowedSubtensor b (fun i ↦ P (sigma.symm i)))
      (permObj sigma (T.basisAllAllowedSubtensor b P)) := by sorry
