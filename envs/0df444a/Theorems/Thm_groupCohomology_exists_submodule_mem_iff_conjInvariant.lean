-- Prove2me | Theorems.Thm_groupCohomology_exists_submodule_mem_iff_conjInvariant
-- name    : groupCohomology.exists_submodule_mem_iff_conjInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5a87ff29-a1a0-5e1a-b94d-876733a2c0b2
-- title:
--   Conjugation-invariant classes in H¹(S,A) form a submodule
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a $k$-linear representation of $G$ (an object of `Rep k G`, with action maps $A.\rho$), and $S$ a subgroup of $G$. Write $\mathrm{Res}_S A$ for the restriction of $A$ along the inclusion $S \hookrightarrow G$, and let `H1π` denote the canonical $k$-linear surjection from the module `cocycles₁` of $1$-cocycles of $\mathrm{Res}_S A$ onto $H^1(S, \mathrm{Res}_S A)$. The assertion is that there exists a $k$-submodule $V$ of $H^1(S, \mathrm{Res}_S A)$ whose elements are exactly those $x$ for which some $1$-cocycle $c$ of $\mathrm{Res}_S A$ satisfies `H1π c = x` and, for every $g \in G$, there is an element $a \in A$ such that for all $s, t \in S$ with $g^{-1} s g = t$ in $G$ one has $A.\rho(g)(c(t)) - c(s) = A.\rho(s)(a) - a$. Thus the set of classes representable by a cocycle that is invariant, up to an explicit coboundary depending only on $g$, under conjugation by every element of $G$ is closed under addition and scalar multiplication and contains $0$. No normality or finite-index hypothesis on $S$ is imposed.
--
--   For $S$ normal in $G$ the membership condition is the cocycle-level form of invariance under the conjugation action of $G/S$ on $H^1(S, A|_S)$, so the submodule produced is the module of $G/S$-invariant classes; the statement is packaged existentially so that a consumer receives the submodule rather than having to build it. It is used in the comparison of ranks of spaces of (continuous) cohomology classes, namely by [`groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq`](thm.html#groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_submodule_mem_iff_conjInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_submodule_mem_iff_conjInvariant
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) :
    ∃ V : Submodule k (H1 (Rep.res S.subtype A)), ∀ x, x ∈ V ↔
      ∃ c : cocycles₁ (Rep.res S.subtype A), H1π _ c = x ∧
        ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
          A.ρ g (c t) - c s = A.ρ (s : G) a - a := by sorry
