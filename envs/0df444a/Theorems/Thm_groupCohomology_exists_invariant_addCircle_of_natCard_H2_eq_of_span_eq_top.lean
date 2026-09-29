-- Prove2me | Theorems.Thm_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
-- name    : groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/de6fec68-463e-5fda-abf8-b498f49728c6
-- title:
--   Invariant maps in degree 2 from a class formation axiom
-- statement:
--   Let $G$ be a finite group, let $X$ be a representation of $G$ over $\mathbb{Z}$ (an object of `Rep ℤ G`, i.e. a $\mathbb{Z}[G]$-module) and let $u \in H^2(G, X)$. Assume two hypotheses. First, for every subgroup $S \le G$ the group $H^2(S, X|_S)$, cohomology of the restricted representation `Rep.res S.subtype X`, is finite of cardinality $|S|$. Second, for every subgroup $S \le G$ the $\mathbb{Z}$-submodule of $H^2(S, X|_S)$ spanned by the image of $u$ under the restriction map `groupCohomology.map S.subtype (𝟙 _) 2` is the whole group, i.e. the restriction of $u$ generates $H^2(S, X|_S)$. Then there exist an additive map $\mathrm{inv}_G \colon H^2(G, X) \to \mathbb{Q}/\mathbb{Z}$ (Lean's `AddCircle (1 : ℚ)`) and, for each subgroup $H \le G$, an additive map $\mathrm{inv}_H \colon H^2(H, X|_H) \to \mathbb{Q}/\mathbb{Z}$, such that: $\mathrm{inv}_G$ and every $\mathrm{inv}_H$ are injective; the range of $\mathrm{inv}_G$ consists exactly of the $t \in \mathbb{Q}/\mathbb{Z}$ with $|G| \cdot t = 0$, and that of $\mathrm{inv}_H$ exactly of the $t$ with $|H| \cdot t = 0$; for every $H$ and every $x \in H^2(G, X)$ one has $\mathrm{inv}_H(\mathrm{res}_H x) = [G : H] \cdot \mathrm{inv}_G(x)$; and $\mathrm{inv}_G(u)$ is the class of $1/|G|$, while $\mathrm{inv}_H(\mathrm{res}_H u)$ is the class of $1/|H|$ for every $H$.
--
--   This is the group-theoretic core of Tate's construction of the invariant map of a class formation in degree $2$: from the orders of the $H^2$ of all subgroups together with a fundamental class restricting to generators, one obtains normalised injections into $\mathbb{Q}/\mathbb{Z}$ compatible with restriction up to the index. It is used in the construction of the global invariant map on the degree-$2$ cohomology of the idèle class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory in

theorem groupCohomology.exists_invariant_addCircle_of_natCard_H2_eq_of_span_eq_top
    {G : Type} [Group G] [Fintype G] (X : Rep ℤ G) (u : groupCohomology X 2)
    (hcard : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype X) 2) = Fintype.card S)
    (hspan : ∀ S : Subgroup G, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom u} = ⊤) :
    ∃ (invG : groupCohomology X 2 →+ AddCircle (1 : ℚ))
      (inv : ∀ H : Subgroup G, groupCohomology (Rep.res H.subtype X) 2 →+ AddCircle (1 : ℚ)),
      Function.Injective invG ∧ (∀ H : Subgroup G, Function.Injective (inv H)) ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card G • t = 0) ∧
      (∀ (H : Subgroup G) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0) ∧
      (∀ (H : Subgroup G) (x : groupCohomology X 2),
        inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom x) = H.index • invG x) ∧
      invG u = (((1 : ℚ) / (Nat.card G : ℚ) : ℚ) : AddCircle (1 : ℚ)) ∧
      (∀ H : Subgroup G, inv H ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype X)) 2).hom u) =
        (((1 : ℚ) / (Nat.card ↥H : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by sorry
