-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T11:30:41.340009+00:00
-- url     : https://prove2.me/theorems/e709d7b3-5875-4b2f-b155-6fba3a650bd0
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has exactly 3|V|−6 edges. A proof route uses Euler’s formula and shows maximality forces every face to be triangular.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
