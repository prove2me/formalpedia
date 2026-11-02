-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:34:18.073194+00:00
-- url     : https://prove2.me/theorems/286e63bc-1c87-47a6-a335-926848b9bcdc
-- title:
--   Planar triangulation extension on the same vertex set
-- statement:
--   Every connected graph with at least three vertices and a drawing satisfying the supplied predicate can be extended, without adding vertices, to a graph with the same kind of drawing and exactly 3|V|−6 edges. The extension contains every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
