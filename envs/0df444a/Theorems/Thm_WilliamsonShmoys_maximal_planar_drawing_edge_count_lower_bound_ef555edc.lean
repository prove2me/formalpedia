-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_ef555edc
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ef555edc
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:44:59.837427+00:00
-- url     : https://prove2.me/theorems/0410eb4b-2165-4dd0-8c4a-7f86b2c7f291
-- title:
--   Lower edge bound for this maximal drawing
-- statement:
--   A drawable graph on at least three vertices with no drawable strict edge extension has at least 3|V| − 6 edges. This removes the maximality and triangulation argument from the parent. Show maximality forces connectedness and triangular faces, then apply Euler’s formula and count face-edge incidences. At |V| = 3, maximality forces the triangle and the bound holds with equality. Formalizing the face and edge-addition arguments for the attached arc predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ef555edc
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  sorry
