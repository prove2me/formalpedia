-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
-- name    : WilliamsonShmoys.planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:33:20.366163+00:00
-- url     : https://prove2.me/theorems/e0c85ed3-29c9-4753-86a9-a6c3e4be15ff
-- title:
--   Planar edge bound for all finite graphs
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing as defined by `HasPlanarDrawingOn` has at most `3|V|−6` edges, regardless of connectedness. This strengthens the target by removing its connectedness hypothesis. The proof route uses Euler’s connected planar edge bound on components of size at least three, direct edge counts for smaller components, and a sum of their deficits.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_bound_all__p2m_412cf563_cd90_4618_ba6d_11be264b4659_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
