-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:43.199339+00:00
-- url     : https://prove2.me/theorems/ce2523b8-2817-4847-92d2-52162bbbf3f4
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing has at most 3|V|−6 edges. A proof route is to obtain face boundary walks from the embedding, count each edge side twice, use that every such boundary has length at least three under these hypotheses, and apply Euler’s formula. The vertex lower bound is essential to rule out the exceptional one-edge boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound__p2m_ce11034e_9d40_4f95_bd08_a8f0a5d53ed0_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
