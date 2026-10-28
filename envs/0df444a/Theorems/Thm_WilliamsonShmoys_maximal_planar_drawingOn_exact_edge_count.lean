-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_exact_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:54:53.11075+00:00
-- url     : https://prove2.me/theorems/054c33ac-9b1d-48cd-a611-951bc7b74b50
-- title:
--   Exact edge count of a maximal planar drawing
-- statement:
--   A connected graph on at least three vertices that has a planar drawing and is maximal among planar supergraphs on the same vertex type has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawingOn_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
