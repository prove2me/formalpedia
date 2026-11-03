-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:42.675194+00:00
-- url     : https://prove2.me/theorems/3c9d29e6-223d-45fd-8079-57d4a2d204ad
-- title:
--   Triangulating a connected planar graph on its vertex set
-- statement:
--   Every connected graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn is a subgraph of a graph on the same vertices that also has such a drawing and has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_triangulation__p2m_ff906063_5ccb_4e8b_ad72_9b52b363ab18_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ HasPlanarDrawingOn M ∧
      (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
       M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
