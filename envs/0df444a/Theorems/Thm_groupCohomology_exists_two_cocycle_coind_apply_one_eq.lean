-- Prove2me | Theorems.Thm_groupCohomology_exists_two_cocycle_coind_apply_one_eq
-- name    : groupCohomology.exists_two_cocycle_coind_apply_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/a7db353a-d428-5aac-85e5-5626e6e16c7f
-- title:
--   Cochain-level Shapiro section for H² of a coinduced module
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $S \le G$ a subgroup and $A$ a $k$-linear representation of $S$. Let $c : (\mathrm{Fin}\,2 \to S) \to A$ be an inhomogeneous $2$-cochain of $S$ with values in $A$ which is a cocycle, i.e. $\mathrm{inhomogeneousCochains.d}\,A\,2\,c = 0$. The assertion is that there exists an inhomogeneous $2$-cochain $F : (\mathrm{Fin}\,2 \to G) \to \mathrm{Coind}$ of $G$ with values in the representation $\mathrm{Coind} =$ `Rep.coind S.subtype A` coinduced along the inclusion $S \hookrightarrow G$ — whose underlying module consists of those functions $f : G \to A$ satisfying $f(s x) = \rho_A(s)\,f(x)$ for all $s \in S$, $x \in G$, with $G$ acting by $(g \cdot f)(x) = f(x g)$ — such that $\mathrm{inhomogeneousCochains.d}\,\mathrm{Coind}\,2\,F = 0$, together with the compatibility that for every $s : \mathrm{Fin}\,2 \to S$ the function underlying $F$ applied to the $G$-valued pair $i \mapsto (s\,i : G)$, evaluated at $1 \in G$, equals $c\,s$. Thus the cocycle $F$ restricted to $S \times S$ and evaluated at the identity recovers $c$ on the nose, at the level of cochains.
--
--   This is the explicit cochain-level section underlying Shapiro's lemma in degree two, $H^2(S,A) \cong H^2(G,\mathrm{Coind}_S^G A)$: Mathlib's comparison isomorphism for coinduced modules is built from resolutions and provides no formula on inhomogeneous cochains, whereas the construction of idelic cocycles requires one. It is used in the construction of a $2$-cocycle on ideles with prescribed local behaviour in the Herbrand-quotient part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_two_cocycle_coind_apply_one_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_two_cocycle_coind_apply_one_eq
    {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) (A : Rep k S)
    (c : (Fin 2 → S) → A) (hc : inhomogeneousCochains.d A 2 c = 0) :
    ∃ (F : (Fin 2 → G) → Rep.coind S.subtype A)
      (_ : inhomogeneousCochains.d (Rep.coind S.subtype A) 2 F = 0),
      ∀ s : Fin 2 → S, (F (fun i => (s i : G))).1 1 = c s := by sorry
