-- Prove2me | Theorems.Thm_groupCohomology_isMulCoboundary2_of_filtration
-- name    : groupCohomology.isMulCoboundary2_of_filtration
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/3137f9eb-cbb2-561c-80e3-30a9f9e306c7
-- title:
--   Degree-two coboundary criterion for complete separated filtrations
-- statement:
--   Let $G$ be a group acting by group automorphisms on a multiplicatively written abelian group $M$, and let $F : \mathbb{N} \to$ (subgroups of $M$) be a family of subgroups with $F_0 = \top$ (all of $M$), each $F_n$ stable under the action ($x \in F_n$ implies $g \cdot x \in F_n$ for all $g \in G$); the family is not assumed to be decreasing. Assume completeness: for every sequence $s : \mathbb{N} \to M$ with $s_{n+1}/s_n \in F_n$ for all $n$ there is $x \in M$ with $x/s_n \in F_n$ for all $n$; and separatedness: if $x \in F_n$ for all $n$ then $x = 1$. Assume further that for each $n$ and each map $f : G \times G \to M$ taking values in $F_n$ and satisfying the multiplicative $2$-cocycle identity there exists $c : G \to M$ with all values in $F_n$ such that $f(g,h)\big/\big((g \cdot c(h))\, c(gh)^{-1} c(g)\big) \in F_{n+1}$ for all $g, h$. Then every $f : G \times G \to M$ satisfying the multiplicative $2$-cocycle identity is a multiplicative $2$-coboundary, i.e. there is $x : G \to M$ with $(g \cdot x(h))\, x(gh)^{-1} x(g) = f(g,h)$ for all $g, h \in G$.
--
--   This is the degree-two successive-approximation (or devissage) lemma: vanishing of $H^2$ with coefficients in a complete separated filtered module follows from vanishing modulo each step of the filtration. It is used in the construction of a subgroup of units on which prescribed cocycles trivialise, in the local-level part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isMulCoboundary2_of_filtration.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.isMulCoboundary2_of_filtration
    {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ (n : ℕ) (g : G) (x : M), x ∈ F n → g • x ∈ F n)
    (hcomplete : ∀ s : ℕ → M, (∀ n, s (n + 1) / s n ∈ F n) → ∃ x : M, ∀ n, x / s n ∈ F n)
    (hsep : ∀ x : M, (∀ n, x ∈ F n) → x = 1)
    (hgr : ∀ (n : ℕ) (f : G × G → M), (∀ x, f x ∈ F n) → IsMulCocycle₂ f →
      ∃ c : G → M, (∀ g, c g ∈ F n) ∧ ∀ g h, f (g, h) / (g • c h / c (g * h) * c g) ∈ F (n + 1))
    (f : G × G → M) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f := by sorry
