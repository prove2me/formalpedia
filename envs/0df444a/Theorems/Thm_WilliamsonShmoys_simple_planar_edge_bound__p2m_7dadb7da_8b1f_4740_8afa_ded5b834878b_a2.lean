-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:30:29.277382+00:00
-- url     : https://prove2.me/theorems/0454f032-4ccd-41fc-a2c2-ee4bb5e266a5
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with at least three vertices and the given planar drawing has at most `3V − 6` edges, expressed without truncated subtraction. The hypothesis `3 ≤ V` handles the small-graph exceptions. A standard route counts face-boundary steps, using at least three steps per face and two sides per edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_7dadb7da_8b1f_4740_8afa_ded5b834878b_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 <= Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
