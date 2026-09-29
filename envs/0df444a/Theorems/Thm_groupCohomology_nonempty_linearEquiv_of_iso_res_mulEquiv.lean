-- Prove2me | Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
-- name    : groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6613b3b0-7db2-5f84-a35a-231a683dbb79
-- title:
--   Transport of Hⁿ along an isomorphism of group–module pairs
-- statement:
--   Let $k$ be a commutative ring, let $G$ and $H$ be groups, let $e : G \simeq^* H$ be an isomorphism of groups, let $A$ be a $k$-linear representation of $G$ and $B$ a $k$-linear representation of $H$, and let $\varphi$ be an isomorphism in the category of $k$-linear representations of $G$ from $A$ to `Rep.res e.toMonoidHom B`, that is, to $B$ regarded as a $G$-representation via the monoid homomorphism underlying $e$. Let $n$ be a natural number. The assertion is that there exists a $k$-linear equivalence $\psi$ from the $n$-th group cohomology $H^n(G,A)$ onto $H^n(H,B)$ whose inverse is given, on every element $x$ of $H^n(H,B)$, by the underlying map of the functoriality morphism `groupCohomology.map` attached to the pair consisting of the monoid homomorphism underlying $e$ and the morphism $\varphi^{-1} : \mathrm{res}_e B \to A$ of $G$-representations, in degree $n$. Thus the conclusion records not merely that the two cohomology modules are isomorphic as $k$-modules, but that the inverse of the exhibited equivalence is pinned to the canonical map $H^n(H,B) \to H^n(G,A)$ induced by $(e,\varphi^{-1})$.
--
--   This is the standard statement that group cohomology, being contravariant in the group and covariant in the coefficient module, is invariant under an isomorphism of pairs $(G,A) \cong (H,B)$. It serves as a transport lemma: results about $H^n$ proved for one model of a Galois group and its coefficient module (for instance an idèle class group, or coefficients restricted along an identification of Galois groups) are carried over to an isomorphic model, and it is used in this form by the Herbrand-quotient and descent computations of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology Rep

theorem groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (A : Rep k G) (B : Rep k H) (φ : A ≅ Rep.res e.toMonoidHom B) (n : ℕ) :
    ∃ ψ : groupCohomology A n ≃ₗ[k] groupCohomology B n,
      ∀ x : groupCohomology B n,
        ψ.symm x = (groupCohomology.map e.toMonoidHom (φ.inv : Rep.res e.toMonoidHom B ⟶ A) n).hom x := by sorry
