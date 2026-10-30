-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_same_vertex_triangulation_with_exact_edge_count
-- name    : WilliamsonShmoys.exists_same_vertex_triangulation_with_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:27:57.077073+00:00
-- url     : https://prove2.me/theorems/154637ce-fcea-4dee-8706-336ac9ae49a3
-- title:
--   Same-vertex planar edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex type with exactly 3|V|−6 edges. The proof can extend the drawing to a maximal planar one by adding noncrossing edges, then count faces using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_same_vertex_triangulation_with_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      N <= K /\
      WilliamsonShmoys.HasPlanarDrawingOn K /\
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
