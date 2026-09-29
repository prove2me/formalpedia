-- Prove2me | Theorems.Thm_groupCohomology_isCoboundary2_of_addEquiv_pi
-- name    : groupCohomology.isCoboundary2_of_addEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d007e9a1-5434-5a2c-aac1-dc12b2d33453
-- title:
--   Every 2-cocycle is a coboundary for a translation module
-- statement:
--   Let $G$ be a group, let $P$ and $P_0$ be additive abelian groups, and let $G$ act on $P$ by a scalar multiplication $\bullet$ (a bare `SMul G P`; no action or distributivity axioms are imposed). Suppose given an additive isomorphism $e : P \cong G \to P_0$ onto the group of all functions from $G$ to $P_0$ with pointwise addition, which intertwines the scalar multiplication on $P$ with left translation of the argument: $e(h \bullet p)(x) = e(p)(h^{-1}x)$ for all $h, x \in G$ and $p \in P$. Let $f : G \times G \to P$ satisfy the inhomogeneous $2$-cocycle identity in the sense of `IsCocycle₂`, that is $f(gh, j) + f(g, h) = g \bullet f(h, j) + f(g, hj)$ for all $g, h, j \in G$. Then $f$ satisfies `IsCoboundary₂`: there is a function $c : G \to P$ with $g \bullet c(h) - c(gh) + c(g) = f(g, h)$ for all $g, h \in G$.
--
--   This is the degree-$2$ instance of the vanishing of cohomology for a module of functions on $G$ with the translation action (an induced, or co-induced, module); the conclusion is the concrete statement that the explicitly given cochain trivialises $f$, not a statement about cohomology groups. It is used in [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle), where a multiplicative $2$-cocycle on such a module has to be split.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isCoboundary2_of_addEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.isCoboundary2_of_addEquiv_pi
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G × G → P) (hf : IsCocycle₂ f) : IsCoboundary₂ f := by sorry
