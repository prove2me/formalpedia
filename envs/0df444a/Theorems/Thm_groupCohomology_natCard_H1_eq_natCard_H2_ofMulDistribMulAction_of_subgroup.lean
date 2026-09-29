-- Prove2me | Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup
-- name    : groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/d175d80b-66e4-50fd-99b0-7e2b8b05ce4c
-- title:
--   Herbrand quotient one for U over a cohomologically trivial V
-- statement:
--   Let $G$ be a finite cyclic group acting on an abelian group $M$ (written multiplicatively) by a multiplicative distributive action, so that each $g \in G$ acts as a group automorphism of $M$. Let $U$ and $V$ be subgroups of $M$ with $V \le U$, both stable under the action elementwise ($g \cdot x \in U$ for all $g \in G$, $x \in U$, and likewise for $V$), and assume that $V$, viewed inside $U$, has finite index. Assume further that $V$ is cohomologically trivial in degrees $1$ and $2$ in the following explicit form: every $f : G \to M$ with all values in $V$ satisfying the multiplicative $1$-cocycle condition `IsMulCocycle₁` is of the form $f(g) = (g \cdot x)/x$ for some $x \in V$; and every $f : G \times G \to M$ with all values in $V$ satisfying the multiplicative $2$-cocycle condition `IsMulCocycle₂` satisfies $f(g,h) = (g \cdot x(h)) \, x(g) / x(gh)$ for some $x : G \to M$ with all values in $V$. Finally, let a multiplicative distributive action of $G$ on the subgroup $U$ be given which is compatible with the action on $M$, i.e. $(g \cdot u : M) = g \cdot (u : M)$ for all $g \in G$, $u \in U$. Then, for the $\mathbb{Z}[G]$-representation `Rep.ofMulDistribMulAction G U` attached to this action, $H^1$ and $H^2$ are both finite and $\#H^1(G,U) = \#H^2(G,U)$.
--
--   This is the statement that the Herbrand quotient $h(U) = \#H^1/\#H^2$ of a cyclic group acting on $U$ equals $1$ whenever $U$ contains a $G$-stable subgroup of finite index with vanishing $H^1$ and $H^2$; it is obtained from the short exact sequence $1 \to V \to U \to U/V \to 1$ together with [`groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite). It serves the computation of norm groups of unit groups in unramified layers, and is used in the proof of the existence of elements of prescribed norm in fields obtained by adjoining roots of unity to a $p$-adic field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup {G : Type} [Group G] [Finite G] [IsCyclic G]
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (U V : Subgroup M) (hVU : V ≤ U) (hUG : ∀ (g : G), ∀ x ∈ U, g • x ∈ U)
    (hVG : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) [(V.subgroupOf U).FiniteIndex]
    (hV1 : ∀ f : G → M, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g)
    (hV2 : ∀ f : G × G → M, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
      ∃ x : G → M, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h))
    [MulDistribMulAction G U] (hcompatU : ∀ (g : G) (u : U), ((g • u : U) : M) = g • (u : M)) :
    Finite (H1 (Rep.ofMulDistribMulAction G U)) ∧ Finite (H2 (Rep.ofMulDistribMulAction G U)) ∧
      Nat.card (H1 (Rep.ofMulDistribMulAction G U)) = Nat.card (H2 (Rep.ofMulDistribMulAction G U)) := by sorry
