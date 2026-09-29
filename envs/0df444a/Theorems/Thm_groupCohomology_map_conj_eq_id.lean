-- Prove2me | Theorems.Thm_groupCohomology_map_conj_eq_id
-- name    : groupCohomology.map_conj_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/9f8ee9a0-2e28-520f-a146-acee5b2fd416
-- title:
--   Inner automorphisms act trivially on group cohomology
-- statement:
--   Let $k$ be a commutative ring, $G$ a group (both in the same universe), $M$ an object of $\mathrm{Rep}\,k\,G$, that is a $k$-linear representation $\rho = M.\rho$ of $G$, let $g \in G$ and let $n$ be a natural number. Write $c_g = (\mathrm{MulAut.conj}\ g)$ for the inner automorphism $h \mapsto g h g^{-1}$ of $G$, viewed as a monoid homomorphism, and let $\mathrm{Rep.res}\ c_g\ M$ be the representation with the same underlying $k$-module as $M$ and with $h$ acting by $\rho(g h g^{-1})$. Let $\varphi$ be a morphism of representations from $\mathrm{Rep.res}\ c_g\ M$ to $M$, and assume that on underlying modules $\varphi$ is given by $m \mapsto \rho(g^{-1}) m$. Then the map induced on cohomology by the pair $(c_g, \varphi)$ through the functoriality `groupCohomology.map` is the identity morphism of $H^n(G, M)$, for every degree $n$ — an equality of morphisms, not merely an equality after passing to cocycle classes.
--
--   This is the classical statement that inner automorphisms of $G$ act trivially on $H^n(G, M)$, in the form in which the pair (conjugation by $g$, multiplication by $\rho(g^{-1})$) induces the identity in every degree. It is used in the Herbrand-quotient part of the development, for instance when transporting classes along Shapiro-type isomorphisms and when comparing local fundamental classes and idelic cohomology classes under conjugation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_conj_eq_id.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.map_conj_eq_id
    {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (g : G) (n : ℕ)
    (φ : Rep.res (MulAut.conj g).toMonoidHom M ⟶ M)
    (hφ : ∀ m : Rep.res (MulAut.conj g).toMonoidHom M, φ.hom m = M.ρ g⁻¹ m) :
    groupCohomology.map (MulAut.conj g).toMonoidHom φ n = 𝟙 (groupCohomology M n) := by sorry
