-- Prove2me | Theorems.Thm_groupCohomology_isZero_H1_res_units_of_smul_eq
-- name    : groupCohomology.isZero_H1_res_units_of_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/ff219f43-594a-5b22-8cec-9cbeb64e5406
-- title:
--   Hilbert 90 for subgroups: vanishing of H¹(S,M^×)
-- statement:
--   Let $E$ and $M$ be fields with $M$ an $E$-algebra that is finite-dimensional over $E$, and suppose the group $M \simeq_{\mathrm{alg}[E]} M$ of $E$-algebra automorphisms of $M$ is equipped with a multiplicative-distributive action on the unit group $M^\times$, i.e. an action by group automorphisms of $M^\times$. Assume this action is the tautological one: for every automorphism $g$ and every unit $a$, the underlying element of $M$ of $g \cdot a$ equals $g(a)$. The conclusion is that for every subgroup $S$ of $M \simeq_{\mathrm{alg}[E]} M$, the degree-one group cohomology of the representation obtained by viewing $M^\times$ additively as a $\mathbb{Z}$-linear representation of $M \simeq_{\mathrm{alg}[E]} M$ via `Rep.ofMulDistribMulAction` and then restricting along the inclusion `S.subtype` of $S$ is a zero object of the ambient category; that is, $H^1(S, M^\times) = 0$, the action of $S$ on $M^\times$ being the restricted one. No separability, normality or Galois hypothesis on $M/E$ is imposed, and $S$ is an arbitrary subgroup.
--
--   This is Noether's form of Hilbert's Theorem 90, in the shape asserting that the restriction of the unit-group representation to an arbitrary subgroup $S$ of $\mathrm{Aut}_E(M)$ has vanishing first cohomology (equivalently, Hilbert 90 for the extension $M/M^S$). In this form it supplies the vanishing hypothesis needed to run the inflation–restriction sequence in degree two, and it is cited by [`IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero`](thm.html#IsGalois.map_two_units_injective_and_exists_of_map_subtype_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isZero_H1_res_units_of_smul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isZero_H1_res_units_of_smul_eq
    (E M : Type) [Field E] [Field M] [Algebra E M] [FiniteDimensional E M]
    [MulDistribMulAction (M ≃ₐ[E] M) Mˣ]
    (hactM : ∀ (g : M ≃ₐ[E] M) (a : Mˣ), ((g • a : Mˣ) : M) = g (a : M)) :
    ∀ S : Subgroup (M ≃ₐ[E] M),
      CategoryTheory.Limits.IsZero
        (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (M ≃ₐ[E] M) Mˣ)) 1) := by sorry
