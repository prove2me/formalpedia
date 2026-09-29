-- Prove2me | Theorems.Thm_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2
-- name    : groupCohomology.cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/fadffb31-bf08-571b-8e61-9ecdbecc1944
-- title:
--   Cup product against connecting cochains is a level coboundary
-- statement:
--   Fix a commutative ring $k$, a group $G$ and a homomorphism $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$), used only to speak of levels. Let $M', M, M'', D'', D, D', N$ be $k$-linear representations of $G$, with morphisms $i \colon M' \to M$ and $\pi \colon M \to M''$ such that $\pi$ is surjective on underlying modules and such that for every $m \in M$ one has $\pi(m) = 0$ if and only if $m$ lies in the image of $i$, and morphisms $\pi_D \colon D'' \to D$ and $i_D \colon D \to D'$ with $i_D$ surjective and $i_D(x) = 0$ if and only if $x$ lies in the image of $\pi_D$ (injectivity of $i$ and of $\pi_D$ is not assumed). Let $\varphi' \colon M' \otimes D' \to N$, $\varphi \colon M \otimes D \to N$, $\varphi'' \colon M'' \otimes D'' \to N$ be $k$-bilinear maps, with $\varphi$ equivariant in the sense that $\varphi(\rho_M(g)m, \rho_D(g)x) = \rho_N(g)\varphi(m,x)$ for all $g, m, x$, and compatible with the maps: $\varphi(i(m'), x) = \varphi'(m', i_D(x))$ and $\varphi(m, \pi_D(v)) = \varphi''(\pi(m), v)$. Let $c \in M''$ be $G$-invariant and let $y$ be a $1$-cocycle of $D'$ satisfying the level-constancy predicate `IsLevelConstant₁ r`. Then the $2$-cochain $(s,t) \mapsto \varphi'\bigl(\delta^0c(s), \rho_{D'}(s)(y(t))\bigr) + \varphi''\bigl(c, \delta^1y(s,t)\bigr)$, where $\delta^0 c =$ `deltaCochain₀ i π hπ c` and $\delta^1 y =$ `deltaCochain₁ πD iD hiD y` are the connecting cochains attached to the two sequences, belongs to `levelCoboundaries₂ r N`.
--
--   This is the cochain-level form of one of the two anticommutativity squares relating a cup-product pairing of a dual pair of extensions to the connecting homomorphisms of the associated long exact sequences: up to sign, $\langle \delta^0 c, y\rangle = -\langle c, \delta^1 y\rangle$ in the relevant degree-$2$ cohomology. It is used in the proof of [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory
open groupCohomology

theorem groupCohomology.cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M' M M'' D'' D D' N : Rep.{u} k G}
    (i : M' ⟶ M) (π : M ⟶ M'') (hπ : Function.Surjective π.hom)
    (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
    (πD : D'' ⟶ D) (iD : D ⟶ D') (hiD : Function.Surjective iD.hom)
    (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
    (φ' : M' →ₗ[k] D' →ₗ[k] N)
    (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (φ'' : M'' →ₗ[k] D'' →ₗ[k] N)
    (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
    (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
    (c : M'') (hc : ∀ s, M''.ρ s c = c)
    (y : cocycles₁ D') (hy : IsLevelConstant₁ r (⇑y)) :
    (cupCochain φ' (deltaCochain₀ i π hπ c) (⇑y)
        + fun st => φ'' c (deltaCochain₁ πD iD hiD (⇑y) st))
      ∈ levelCoboundaries₂ r N := by sorry
