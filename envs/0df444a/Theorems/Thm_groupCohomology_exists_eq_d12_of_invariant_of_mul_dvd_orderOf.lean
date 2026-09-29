-- Prove2me | Theorems.Thm_groupCohomology_exists_eq_d12_of_invariant_of_mul_dvd_orderOf
-- name    : groupCohomology.exists_eq_d12_of_invariant_of_mul_dvd_orderOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b27a6dd1-ea68-5aa6-acd0-2339680e79af
-- title:
--   Inflated 2-cocycle with p-torsion coefficients is a coboundary
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a representation of $G$ over $k$. Assume a natural number $p$ (not assumed prime) annihilates $A$, i.e. $p \cdot a = 0$ for every $a \in A$. Let $N \trianglelefteq G$ be a normal subgroup acting trivially, $A.\rho\,n = 1$ for all $n \in N$, and let $\varphi \in G$ be such that every $g \in G$ satisfies $(\varphi^i)^{-1} g \in N$ for some natural $i$ (so the image of $\varphi$ generates $G/N$ by non-negative powers), the image $\bar\varphi \in G/N$ being of finite order. Let $e$ be a natural number with $p \cdot e \mid \operatorname{ord}(\bar\varphi)$. Finally let $E : G \times G \to A$ be an inhomogeneous $2$-cocycle, i.e. $E(gh,j) + E(g,h) = A.\rho\,g\,(E(h,j)) + E(g,hj)$, satisfying the periodicity $E(g\varphi^e, h) = E(g,h)$ and right $N$-invariance in each variable, $E(gn,h) = E(g,h)$ and $E(g,hn) = E(g,h)$ for $n \in N$. The conclusion is that $E$ is the coboundary of an $N$-invariant $1$-cochain: there exists $b : G \to A$ with $b(gn) = b(g)$ for all $g \in G$, $n \in N$, and $E(g,h) = A.\rho\,g\,(b(h)) - b(gh) + b(g)$ for all $g,h$.
--
--   This is the cochain-level form of the vanishing of the inflated second cohomology of a finite cyclic quotient acting on $p$-torsion coefficients, in the situation where the cocycle already has period $e$ with $pe$ dividing the order of the cyclic quotient. It is used in the isotropy statement [`groupCohomology.theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified`](thm.html#groupCohomology.theta1_apply_eq_zero_of_mem_unramified_of_mem_unramified) for unramified classes under the local pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_eq_d12_of_invariant_of_mul_dvd_orderOf.lean

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_eq_d12_of_invariant_of_mul_dvd_orderOf
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (p : ℕ) (hpA : ∀ a : A, p • a = 0)
    (N : Subgroup G) [N.Normal] (hN : ∀ n ∈ N, A.ρ n = 1)
    (φ : G) (hgen : ∀ g : G, ∃ i : ℕ, (φ ^ i)⁻¹ * g ∈ N)
    (hfin : IsOfFinOrder (QuotientGroup.mk φ : G ⧸ N))
    (e : ℕ) (hdiv : p * e ∣ orderOf (QuotientGroup.mk φ : G ⧸ N))
    (E : G × G → A) (hE : E ∈ cocycles₂ A)
    (hEe : ∀ g h : G, E (g * φ ^ e, h) = E (g, h))
    (hE₁ : ∀ g h n : G, n ∈ N → E (g * n, h) = E (g, h))
    (hE₂ : ∀ g h n : G, n ∈ N → E (g, h * n) = E (g, h)) :
    ∃ b : G → A, (∀ g n : G, n ∈ N → b (g * n) = b g) ∧
      ∀ g h : G, E (g, h) = A.ρ g (b h) - b (g * h) + b g := by sorry
