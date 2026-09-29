-- Prove2me | Theorems.Thm_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective
-- name    : groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/9ece93dd-1fe3-5194-98bf-511857353f7c
-- title:
--   Exactness of Hⁿ at the middle term, on elements
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and let $X_1, X_2, X_3$ be $k$-linear representations of $G$ (objects of `Rep k G` in the base universe). Given morphisms $j : X_1 \to X_2$ and $\pi : X_2 \to X_3$ of representations, assume that the underlying $k$-linear map of $j$ is injective, that the underlying $k$-linear map of $\pi$ is surjective, and that for every $y$ in the underlying module $X_2.V$ one has $\pi(y) = 0$ if and only if $y$ lies in the range of $j$; thus $0 \to X_1 \to X_2 \to X_3 \to 0$ is a short exact sequence of representations, with the exactness hypotheses phrased pointwise rather than categorically. Then for every natural number $n$ and every class $y \in H^n(G, X_2)$ whose image under the map on group cohomology induced by the identity of $G$ and $\pi$ vanishes, there exists $x \in H^n(G, X_1)$ whose image under the map induced by the identity of $G$ and $j$ equals $y$. This is exactness of the long exact cohomology sequence at $H^n(G,X_2)$, stated as a surjectivity-onto-the-kernel assertion on elements, in one direction only.
--
--   This is the middle-term exactness of the long exact sequence in group cohomology attached to a short exact sequence of $G$-modules, packaged so that it can be applied directly to elements from value-level hypotheses. It is used in the idelic local-invariant computations, where a class in degree two killed by the map to the idèle class group is lifted back to the cohomology of the multiplicative group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective
    {k G : Type} [CommRing k] [Group G] {X₁ X₂ X₃ : Rep.{0} k G} (j : X₁ ⟶ X₂) (π : X₂ ⟶ X₃)
    (hj : Function.Injective j.hom) (hπ : Function.Surjective π.hom)
    (hexact : ∀ y : X₂.V, π.hom y = 0 ↔ y ∈ Set.range j.hom)
    (n : ℕ) (y : groupCohomology X₂ n) (hy : (groupCohomology.map (MonoidHom.id G) π n).hom y = 0) :
    ∃ x : groupCohomology X₁ n, (groupCohomology.map (MonoidHom.id G) j n).hom x = y := by sorry
