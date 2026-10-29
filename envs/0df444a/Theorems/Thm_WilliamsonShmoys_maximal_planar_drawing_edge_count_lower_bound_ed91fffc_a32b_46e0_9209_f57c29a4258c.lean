-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:23:37.617421+00:00
-- url     : https://prove2.me/theorems/5e8d72d7-7f4f-4c8d-bfbe-517203df2ad7
-- title:
--   Maximal planar drawing edge-count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex set has at least 3|V| − 6 edges. A proof route extends the drawing to a triangulation on the same vertices, applies maximality to identify the extension with M, then counts triangular face-edge incidences using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall K : SimpleGraph V, M <= K ->
      WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    (3 : Int) * (Fintype.card V : Int) - 6 <=
      (M.edgeSet.ncard : Int) := by sorry
