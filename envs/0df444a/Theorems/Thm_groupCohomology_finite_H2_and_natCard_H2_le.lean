-- Prove2me | Theorems.Thm_groupCohomology_finite_H2_and_natCard_H2_le
-- name    : groupCohomology.finite_H2_and_natCard_H2_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/4ce1ec4a-c4ef-5618-aba9-2b0b9f1d4450
-- title:
--   Finiteness and bound for H²(G,A) from H²(G/S,A^S) and H²(S,A)
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $A$ be a $k$-linear representation of $G$, and let $S$ be a normal subgroup of $G$. Assume that the first cohomology $H^1(S, A)$ of the restricted representation `Rep.res S.subtype A` is a subsingleton (that is, $H^1(S,A)=0$), and that the two $k$-modules $H^2(G/S, A^S)$ — cohomology of the quotient group acting on the $S$-invariants, `A.quotientToInvariants S` — and $H^2(S,A)$ are finite. Then $H^2(G,A)$ is finite and its cardinality satisfies $$\#H^2(G,A) \le \#H^2(G/S, A^S)\cdot \#H^2(S,A),$$ the cardinalities being `Nat.card` of the respective cohomology modules. Both assertions are delivered as a single conjunction, the finiteness statement as a `Finite` instance on `H2 A`.
--
--   This is the counting consequence of exactness of the degree-two inflation–restriction sequence $0 \to H^2(G/S, A^S) \to H^2(G,A) \to H^2(S,A)$, valid when $H^1(S,A)$ vanishes. It feeds an induction along a normal series with solvable quotient, [`groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable`](thm.html#groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable), used in turn for the local bound $\# H^2(\mathrm{Gal}(L/K), L^\times) \le [L:K]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_H2_and_natCard_H2_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

theorem groupCohomology.finite_H2_and_natCard_H2_le
    {k G : Type u} [CommRing k] [Group G]
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))]
    [Finite (H2 (A.quotientToInvariants S))] [Finite (H2 (Rep.res S.subtype A))] :
    Finite (H2 A) ∧
      Nat.card (H2 A) ≤ Nat.card (H2 (A.quotientToInvariants S)) * Nat.card (H2 (Rep.res S.subtype A)) := by sorry
