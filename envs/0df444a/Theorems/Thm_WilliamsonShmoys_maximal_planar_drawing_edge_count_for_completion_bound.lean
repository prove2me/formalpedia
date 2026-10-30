-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_completion_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:53:52.894006+00:00
-- url     : https://prove2.me/theorems/ef555edc-d480-4165-8dfb-341a5821827f
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict edge extension on the same vertex type has exactly 3|V| − 6 edges. The n ≥ 3 hypothesis is essential for this count; at n = 3, maximality forces all three edges. This removes the Euler-counting step from the parent. A proof route is to use the drawing to obtain a plane embedding, show maximality forces connectedness and triangular faces (including the outer face), apply Euler’s formula, and count face-edge incidences to get 3f = 2m and hence m = 3n − 6. The remaining core is formalizing those topological facts from the attached arc-based drawing predicate and its exact endpoint/intersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_completion_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
