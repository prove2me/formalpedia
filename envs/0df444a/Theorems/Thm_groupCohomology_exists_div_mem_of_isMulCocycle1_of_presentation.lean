-- Prove2me | Theorems.Thm_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation
-- name    : groupCohomology.exists_div_mem_of_isMulCocycle1_of_presentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/faadec22-a13c-59ad-b72c-897ccf8796f7
-- title:
--   Cocycles with values in Fₙ are coboundaries modulo Fₙ₊₁
-- statement:
--   Let $G$ be a group, $M$ a multiplicatively written abelian group on which $G$ acts by group automorphisms, and $P$ an additively written abelian group equipped with a scalar action of $G$ (no compatibility of this action with the addition of $P$ is assumed). Let $\mathrm{Fn}$ and $\mathrm{Fn1}$ be subgroups of $M$, with $\mathrm{Fn}$ stable under the $G$-action: $g \cdot x \in \mathrm{Fn}$ whenever $x \in \mathrm{Fn}$. Let $\pi : M \to P$ be a function which, on $\mathrm{Fn}$, is multiplicative-to-additive ($\pi(xy) = \pi x + \pi y$ for $x, y \in \mathrm{Fn}$), maps $\mathrm{Fn}$ onto all of $P$ (every $p \in P$ is $\pi x$ for some $x \in \mathrm{Fn}$), has kernel $\mathrm{Fn1}$ in the sense that for $x \in \mathrm{Fn}$ one has $\pi x = 0$ if and only if $x \in \mathrm{Fn1}$, and is equivariant: $\pi(g \cdot x) = g \cdot \pi x$ for $x \in \mathrm{Fn}$. Assume further that every map $f : G \to P$ satisfying the additive $1$-cocycle identity `IsCocycle₁` satisfies `IsCoboundary₁`, i.e. is of the form $g \mapsto g \cdot x - x$. Then for every $f : G \to M$ with $f(g) \in \mathrm{Fn}$ for all $g$ and satisfying the multiplicative $1$-cocycle identity `IsMulCocycle₁`, there exists $a \in \mathrm{Fn}$ such that $f(g) \big/ \big((g \cdot a)/a\big) \in \mathrm{Fn1}$ for all $g \in G$.
--
--   This is the transfer step in a dévissage of $1$-cocycles along a $G$-stable filtration: the subgroups $\mathrm{Fn} \supseteq \mathrm{Fn1}$ are two successive levels, and $P$ presents the graded piece $\mathrm{Fn}/\mathrm{Fn1}$ as an additive $G$-module whose first cohomology vanishes, so that a cocycle with values in $\mathrm{Fn}$ can be corrected by a coboundary into the next level. It feeds the successive-approximation argument used in [`ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle`](thm.html#ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.exists_div_mem_of_isMulCocycle1_of_presentation
    {G M P : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M] [AddCommGroup P] [SMul G P]
    (Fn Fn1 : Subgroup M) (hstab : ∀ (g : G) (x : M), x ∈ Fn → g • x ∈ Fn)
    (π : M → P) (hπmul : ∀ x y, x ∈ Fn → y ∈ Fn → π (x * y) = π x + π y)
    (hπsurj : ∀ p : P, ∃ x ∈ Fn, π x = p)
    (hπker : ∀ x, x ∈ Fn → (π x = 0 ↔ x ∈ Fn1))
    (hπsmul : ∀ (g : G) (x : M), x ∈ Fn → π (g • x) = g • π x)
    (hP : ∀ f : G → P, IsCocycle₁ f → IsCoboundary₁ f)
    (f : G → M) (hfF : ∀ g, f g ∈ Fn) (hf : IsMulCocycle₁ f) :
    ∃ a ∈ Fn, ∀ g, f g / (g • a / a) ∈ Fn1 := by sorry
