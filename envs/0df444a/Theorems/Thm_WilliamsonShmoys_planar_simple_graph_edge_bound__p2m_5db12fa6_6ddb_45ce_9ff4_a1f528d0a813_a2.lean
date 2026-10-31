-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:29:02.892995+00:00
-- url     : https://prove2.me/theorems/7f93d6a5-e061-4fd9-b77a-4e628bac87b4
-- title:
--   Edge bound for a connected graph with a crossing-free drawing
-- statement:
--   A finite connected simple graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges. This is the substantive planar bound needed by the parent. The proof route is to formalize the plane-embedding and Euler face-count argument for the supplied drawing predicate; the remaining core obligation is that formalization.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
