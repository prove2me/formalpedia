-- Prove2me | Theorems.Thm_groupCohomology_isMulCoboundary1_of_filtration
-- name    : groupCohomology.isMulCoboundary1_of_filtration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/bd24a76d-d0b2-5194-a611-b792f74f55a6
-- title:
--   Vanishing of multiplicative 1-cocycles for a complete separated filtration
-- statement:
--   Let $G$ be a group and $M$ a commutative group written multiplicatively, carrying an action of $G$ by group automorphisms. Let $F : \mathbb{N} \to$ (subgroups of $M$) be a family of subgroups subject to four conditions: $F_0 = M$; each $F_n$ is $G$-stable, i.e. $g \cdot x \in F_n$ whenever $x \in F_n$; the family is complete, in the sense that every sequence $s : \mathbb{N} \to M$ with $s_{n+1}/s_n \in F_n$ for all $n$ admits an $x \in M$ with $x/s_n \in F_n$ for all $n$; and it is separated, in the sense that $\bigcap_n F_n = \{1\}$. Assume further that the graded correction property holds: for every $n$ and every $f : G \to M$ with all values in $F_n$ satisfying the multiplicative $1$-cocycle identity $f(gh) = (g \cdot f(h))\, f(g)$, there exists $a \in F_n$ with $f(g)\big/(g \cdot a / a) \in F_{n+1}$ for all $g$. Then every map $f : G \to M$ satisfying the same $1$-cocycle identity is a $1$-coboundary: there is $x \in M$ with $g \cdot x / x = f(g)$ for all $g \in G$. No monotonicity of $n \mapsto F_n$ is assumed.
--
--   This is the standard successive-approximation lemma for $H^1$ of a group acting on a complete separated filtered abelian group: cohomological triviality of the graded steps forces $H^1$ to vanish. It is used in the construction of subgroups of units all of whose associated $1$-cocycles are coboundaries, via [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isMulCoboundary1_of_filtration.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.isMulCoboundary1_of_filtration
    {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ (n : ℕ) (g : G) (x : M), x ∈ F n → g • x ∈ F n)
    (hcomplete : ∀ s : ℕ → M, (∀ n, s (n + 1) / s n ∈ F n) → ∃ x : M, ∀ n, x / s n ∈ F n)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 1)
    (hgr : ∀ (n : ℕ) (f : G → M), (∀ g, f g ∈ F n) → IsMulCocycle₁ f →
      ∃ a ∈ F n, ∀ g, f g / (g • a / a) ∈ F (n + 1))
    (f : G → M) (hf : IsMulCocycle₁ f) : IsMulCoboundary₁ f := by sorry
