-- Prove2me | Theorems.Thm_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
-- name    : groupCohomology.exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5af0d744-ee23-5990-9afe-d3eb5c73a10a
-- title:
--   Cochain-level Shapiro lemma in degree two for permutation modules
-- statement:
--   Let $G$ be a finite group acting on a type $X$, and let $\mathbb{Z}[X]$ denote the finitely supported functions $X \to \mathbb{Z}$, with $g \in G$ acting by push-forward of the support along $x \mapsto g \cdot x$ (in Lean, `Finsupp.mapDomain (g • ·)`). Let $\nu : G \times G \to \mathbb{Z}[X]$ be a function satisfying the inhomogeneous $2$-cocycle identity $g \cdot \nu(h,k) - \nu(gh,k) + \nu(g,hk) - \nu(g,h) = 0$ for all $g,h,k \in G$. Assume further that $\nu$ is locally a coboundary at every point: for each $x_0 \in X$ there is a function $\beta$ from the stabiliser $\mathrm{Stab}_G(x_0)$ to $\mathbb{Z}$ with $\nu(s,t)(x_0) = \beta(s) + \beta(t) - \beta(st)$ for all $s,t \in \mathrm{Stab}_G(x_0)$, i.e. the $\mathbb{Z}$-valued $2$-cocycle obtained by restricting $\nu$ to the stabiliser and evaluating at $x_0$ (trivial action on $\mathbb{Z}$) is the coboundary of $-\beta$. The conclusion is that $\nu$ is a coboundary globally: there exists $\mu : G \to \mathbb{Z}[X]$ with $\nu(g,h) = g \cdot \mu(h) - \mu(gh) + \mu(g)$ for all $g,h \in G$. No normalisation of $\nu$ or of the $\beta$'s is assumed, and $\mu$ is not asserted to be unique.
--
--   This is Shapiro's lemma in degree $2$ for the permutation module $\mathbb{Z}[X] = \bigoplus_{\text{orbits}} \mathbb{Z}[G/G_{x_0}]$, stated at the level of cochains rather than as an isomorphism of cohomology groups: a $2$-cocycle with values in $\mathbb{Z}[X]$ is a coboundary as soon as each of its stabiliser components is. It is used in the construction of ideles attached to an $S$-set, via [`NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero`](thm.html#NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem groupCohomology.exists_forall_eq_mapDomain_smul_sub_add_of_forall_stabilizer
    {G : Type} [Group G] [Finite G] {X : Type} [MulAction G X]
    (ν : G → G → X →₀ ℤ)
    (hν : ∀ g h k : G, Finsupp.mapDomain (g • ·) (ν h k) - ν (g * h) k + ν g (h * k) - ν g h = 0)
    (hloc : ∀ x₀ : X, ∃ β : ↥(MulAction.stabilizer G x₀) → ℤ,
      ∀ s t : ↥(MulAction.stabilizer G x₀), ν s t x₀ = β s + β t - β (s * t)) :
    ∃ μ : G → X →₀ ℤ, ∀ g h : G, ν g h = Finsupp.mapDomain (g • ·) (μ h) - μ (g * h) + μ g := by sorry
