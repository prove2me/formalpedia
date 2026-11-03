-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1
-- name    : WilliamsonShmoys.triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:55:45.055861+00:00
-- url     : https://prove2.me/theorems/f3a63840-9387-418b-904c-fbe2e8408361
-- title:
--   Triangulate a connected planar drawing on the same vertices
-- statement:
--   Every connected finite simple graph on at least three vertices with the specified crossing-free drawing is a subgraph of a graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, K ≤ H ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
