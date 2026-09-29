-- Prove2me | Theorems.Thm_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable
-- name    : groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/98a27e39-068b-5e9e-b5ba-8473f1b31a2c
-- title:
--   Dévissage bound #H²(G,A)≤#G for solvable G
-- statement:
--   Let $G$ be a finite solvable group and let $A$ be a representation of $G$ over $\mathbb{Z}$, i.e. an object of `Rep ℤ G` (a $\mathbb{Z}[G]$-module), with both $G$ and the underlying module in universe $0$. Two hypotheses are imposed, subgroups being presented as injective homomorphisms into $G$. First (`h90`): for every finite group $H$ and every injective homomorphism $\varphi : H \to G$, the first cohomology $H^1$ of the restriction `Rep.res φ A` of $A$ along $\varphi$ is a subsingleton, i.e. vanishes. Second (`hcyc`): for every finite group $H$, every injective $\varphi : H \to G$ and every normal subgroup $N \le H$ whose quotient $H/N$ has prime cardinality, the second cohomology of the $H/N$-representation on the $N$-invariants of `Rep.res φ A` is finite and its cardinality is at most $\#(H/N)$. The conclusion is that $H^2(G,A)$ is finite and $\#H^2(G,A) \le \#G$.
--
--   This is the abstract dévissage behind the local second inequality $\#H^2(\mathrm{Gal}(L/K),L^\times)\le[L:K]$: the input is the vanishing of $H^1$ on every layer (Hilbert 90) together with the inequality on layers of prime degree, and solvability of the group. It is used for the corresponding bound on $H^2$ of the unit group in the local theory and for the bound on $H^2$ of the idèle class group for $p$-groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable
    {G : Type} [Group G] [Finite G] [Group.IsSolvable G] (A : Rep.{0} ℤ G)
    (h90 : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      Subsingleton (H1 (Rep.res φ A)))
    (hcyc : ∀ (H : Type) [Group H] [Finite H] (φ : H →* G), Function.Injective φ →
      ∀ (N : Subgroup H) [N.Normal], (Nat.card (H ⧸ N)).Prime →
        Finite (H2 ((Rep.res φ A).quotientToInvariants N)) ∧
          Nat.card (H2 ((Rep.res φ A).quotientToInvariants N)) ≤ Nat.card (H ⧸ N)) :
    Finite (H2 A) ∧ Nat.card (H2 A) ≤ Nat.card G := by sorry
