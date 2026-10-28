-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:02:35.654809+00:00
-- url     : https://prove2.me/theorems/57da26e6-40fa-4eeb-a0ea-166241e54306
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges. This isolates the topological edge-count argument from the parent. The independent route is to show maximality forces every face of a plane embedding to be triangular, then use Euler’s formula and count the two face sides incident to each edge. The lower bound on the vertex count is retained for the stated formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing_for_triangulation_exact_edge_count {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
