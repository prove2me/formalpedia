-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:49:08.479968+00:00
-- url     : https://prove2.me/theorems/98ef7ab8-2597-47ef-b994-1be56f6b94b5
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   A connected simple graph with the supplied planar drawing and at least three vertices has at most `3n − 6` edges. A proof route is to use the face-boundary count, where every face boundary has length at least three and every edge contributes two sides, then combine that count with Euler’s formula. Bridges contribute both sides to their boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_a18184f7_c783_4d00_9241_7e8764df5618_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (M.edgeFinset.card : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 6 := by sorry
