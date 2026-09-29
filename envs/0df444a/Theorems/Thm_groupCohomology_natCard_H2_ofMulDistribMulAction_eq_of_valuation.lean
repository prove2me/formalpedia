-- Prove2me | Theorems.Thm_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation
-- name    : groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/25b32579-ad01-586b-87a6-df44bc1a7b48
-- title:
--   Order of H² equals #G under an invariant valuation
-- statement:
--   Let $G$ be a finite cyclic group acting by group automorphisms on a commutative group $M$ (written multiplicatively, the action given by a `MulDistribMulAction`), and let $v : M \to \mathbb{Z}$ be a surjective homomorphism into $\mathbb{Z}$ written multiplicatively which is $G$-invariant, i.e. $v(g \cdot x) = v(x)$ for all $g \in G$, $x \in M$. Let $U$ and $V$ be subgroups of $M$ such that $U$ is exactly the kernel of $v$ (membership $x \in U$ holds precisely when $v(x) = 1$), with $V \le U$, with $V$ stable under the action ($g \cdot x \in V$ for $g \in G$ and $x \in V$), and with $V$ of finite index inside $U$. Assume three cochain-level vanishing hypotheses: first, every $V$-valued $1$-cocycle $f : G \to M$ (in Mathlib's multiplicative sense) is of the form $f(g) = (g \cdot x)/x$ for some $x \in V$; second, every $V$-valued $2$-cocycle $f : G \times G \to M$ satisfies $f(g,h) = (g \cdot x_h)/x_{gh} \cdot x_g$ for some family $x : G \to M$ with all $x_g \in V$; third, every $1$-cocycle $f : G \to M$ with values in all of $M$ is a $1$-coboundary. Then the conclusion is the equality of natural numbers $\#H^2(G, M) = \#G$, where $H^2$ is the second group cohomology of the representation `Rep.ofMulDistribMulAction G M` of $G$ on $M$ over $\mathbb{Z}$ and both sides are the cardinalities in Mathlib's sense.
--
--   This is the purely group-theoretic core of the local cyclic "second inequality" with equality: for a cyclic extension $L/K$ of local fields one takes $M = L^{\times}$, $G = \mathrm{Gal}(L/K)$, $v$ the normalised valuation, $U = \mathcal{O}_L^{\times}$, $V$ a cohomologically trivial open subgroup of the units, and Hilbert 90 for the last hypothesis, obtaining $\# H^2(\mathrm{Gal}(L/K), L^{\times}) = [L:K]$. It is used for the computation of $H^2$ of the units in a cyclic local extension at the local level of the argument, via dévissage along the short exact sequences $1 \to V \to U \to U/V \to 1$ and $1 \to U \to M \to \mathbb{Z} \to 0$ together with [`groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite) and [`groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial`](thm.html#groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (v : M →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvG : ∀ (g : G) (x : M), v (g • x) = v x)
    (U V : Subgroup M) (hU : ∀ x, x ∈ U ↔ v x = 1) (hVU : V ≤ U)
    (hVG : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) [(V.subgroupOf U).FiniteIndex]
    (hV1 : ∀ f : G → M, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g)
    (hV2 : ∀ f : G × G → M, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
      ∃ x : G → M, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h))
    (h90 : ∀ f : G → M, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
    Nat.card (H2 (Rep.ofMulDistribMulAction G M)) = Nat.card G := by sorry
