-- Prove2me | Theorems.Thm_groupCohomology_isCoboundary1_of_addEquiv_pi
-- name    : groupCohomology.isCoboundary1_of_addEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0fe5efed-5c4a-549d-9baf-c8620fea23c3
-- title:
--   Cocycles into a translation module are coboundaries
-- statement:
--   Let $G$ be a group, let $P$ and $P_0$ be additive abelian groups, and let $G$ act on $P$ through a scalar multiplication (no compatibility with the addition of $P$ being assumed beyond what follows). Suppose given an isomorphism of additive groups $e : P \simeq (G \to P_0)$ onto the group of all $P_0$-valued functions on $G$ with pointwise addition, which transports the $G$-action into left translation: $e(h \cdot p)(x) = e(p)(h^{-1}x)$ for all $h, x \in G$ and $p \in P$. Let $f : G \to P$ be a function satisfying the inhomogeneous $1$-cocycle identity $f(gh) = f(g) + g \cdot f(h)$ for all $g, h \in G$ (Mathlib's elementwise `IsCocycle₁`). Then $f$ is a $1$-coboundary in the elementwise sense `IsCoboundary₁`: there exists $b \in P$ with $g \cdot b - b = f(g)$ for every $g \in G$. No finiteness or topological hypothesis on $G$ is imposed, and $P$ carries only a `SMul G P` structure, not a $\mathbb{Z}[G]$-module structure.
--
--   This is the vanishing of the first cohomology of a module of all functions on $G$ with values in an abelian group, $G$ acting by translation — the coinduced, or for finite $G$ induced, module from the trivial subgroup — in the explicit elementwise formulation. It is used for the graded pieces of the filtration of local units in the proof of [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isCoboundary1_of_addEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.isCoboundary1_of_addEquiv_pi
    {G P P₀ : Type*} [Group G] [AddCommGroup P] [AddCommGroup P₀] [SMul G P]
    (e : P ≃+ (G → P₀)) (he : ∀ (h : G) (p : P) (x : G), e (h • p) x = e p (h⁻¹ * x))
    (f : G → P) (hf : IsCocycle₁ f) : IsCoboundary₁ f := by sorry
