-- Prove2me | Theorems.Thm_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
-- name    : connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/7d1b2bf9-fabd-5627-87a1-5e8907d59410
-- title:
--   Connected component of (A∩ B)ᶜ through a point of A∖ B
-- statement:
--   Let $X$ be a topological space and let $A, B \subseteq X$ be subsets, both assumed closed, whose union is all of $X$. Assume further that the difference $A \setminus B$ is preconnected, and let $e$ be a point of $X$ lying in $A \setminus B$, that is, $e \in A$ and $e \notin B$. The conclusion is an equality of subsets of $X$: the connected component of $e$ inside the subset $(A \cap B)^{c}$, in the sense of Mathlib's `connectedComponentIn` (the connected component of $e$ in the subspace $(A\cap B)^{c}$, pushed forward to $X$), equals $A \cap (A \cap B)^{c}$. Since $A$ is covered by $A \cap B$ and $A \setminus B$, this right-hand side is exactly $A \setminus B$; the statement is phrased with the intersection with the complement rather than with the set difference.
--
--   An elementary point-set fact: when $X$ is the union of two closed sets $A$ and $B$, the open set $(A \cap B)^{c}$ is the disjoint union of the relatively clopen pieces $A \setminus B$ and $B \setminus A$, so a preconnected piece containing $e$ is the whole connected component of $e$. It is used in the analysis of degenerations of a two-component fibre, where $A$ and $B$ are the two components and $(A\cap B)^{c}$ the locus away from their intersection: it is cited by [`ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth`](thm.html#ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth) and [`ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq`](thm.html#ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem connectedComponentIn_compl_inter_eq_of_isClosed_of_union_eq_univ
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : A ∪ B = Set.univ) (hA' : IsPreconnected (A \ B)) {e : X} (he : e ∈ A \ B) :
    connectedComponentIn (A ∩ B)ᶜ e = A ∩ (A ∩ B)ᶜ := by sorry
