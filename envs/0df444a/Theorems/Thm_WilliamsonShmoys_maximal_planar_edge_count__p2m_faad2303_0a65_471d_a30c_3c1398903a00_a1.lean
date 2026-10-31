-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:54.930968+00:00
-- url     : https://prove2.me/theorems/d1b6a74a-dd8a-4218-af86-64a379555708
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable finite simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
