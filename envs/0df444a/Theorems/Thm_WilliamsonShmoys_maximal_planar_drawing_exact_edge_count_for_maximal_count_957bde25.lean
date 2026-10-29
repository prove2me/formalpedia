-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:11:14.256054+00:00
-- url     : https://prove2.me/theorems/a4b88a5e-be4a-456c-8acd-6e1934740580
-- title:
--   Maximal drawable graphs have exactly the triangulated edge count
-- statement:
--   A drawable simple graph that is maximal among drawable supergraphs on the same finite vertex set, with at least three vertices, has exactly 3|V|−6 edges. Maximality forces every face in its plane embedding to be triangular; Euler’s formula then gives the count, including the three-vertex triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_maximal_count_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ M : SimpleGraph V, K ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
