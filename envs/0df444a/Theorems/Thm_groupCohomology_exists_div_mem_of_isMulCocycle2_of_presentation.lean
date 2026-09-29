-- Prove2me | Theorems.Thm_groupCohomology_exists_div_mem_of_isMulCocycle2_of_presentation
-- name    : groupCohomology.exists_div_mem_of_isMulCocycle2_of_presentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/487f8a44-bd15-5653-8bce-4c3bf34397eb
-- title:
--   Lifting a 2-cocycle through a presented filtration step
-- statement:
--   Let $G$ be a group, $M$ a commutative group written multiplicatively with a $G$-action by group automorphisms, and $P$ an additive commutative group equipped with a scalar multiplication by $G$ (no compatibility of that action with the addition of $P$ being assumed). Let $F_n$ and $F_{n+1}$ be subgroups of $M$, with $F_n$ stable under the action: $g \cdot x \in F_n$ whenever $x \in F_n$. Let $\pi : M \to P$ be a map which, on $F_n$, is additive ($\pi(xy) = \pi x + \pi y$ for $x, y \in F_n$), is surjective in the sense that every $p \in P$ is $\pi x$ for some $x \in F_n$, satisfies $\pi(g \cdot x) = g \cdot \pi x$ for $x \in F_n$, and has $\pi x = 0 \iff x \in F_{n+1}$ for $x \in F_n$. Assume further that every additive $2$-cocycle $G \times G \to P$ in Mathlib's elementwise sense is an additive $2$-coboundary. Then for every $f : G \times G \to M$ with all values in $F_n$ satisfying the multiplicative $2$-cocycle identity, there is a map $c : G \to M$ with $c(g) \in F_n$ for all $g$ and $$f(g,h) \big( (g \cdot c(h)) \, c(gh)^{-1} \, c(g) \big)^{-1} \in F_{n+1} \qquad \text{for all } g, h \in G.$$
--
--   This is the degree-two comparison step for a $G$-stable filtration of $M$: the quotient $F_n/F_{n+1}$ is presented by the group $P$ through $\pi$, and vanishing of $H^2(G, P)$ in the elementwise cocycle/coboundary formulation lets a $2$-cocycle with values in $F_n$ be trivialised modulo $F_{n+1}$. It feeds the graded hypothesis of a successive-approximation construction of subgroups of units on which a prescribed family of multiplicative cocycles is realised.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_div_mem_of_isMulCocycle2_of_presentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.exists_div_mem_of_isMulCocycle2_of_presentation
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
    (Fn Fn1 : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G × G → P, IsCocycle₂ f → IsCoboundary₂ f)
    (f : G × G → M) (hfF : ∀ x, f x ∈ Fn) (hf : IsMulCocycle₂ f) :
    ∃ c : G → M, (∀ g, c g ∈ Fn) ∧ ∀ g h, f (g, h) / (g • c h / c (g * h) * c g) ∈ Fn1 := by sorry
