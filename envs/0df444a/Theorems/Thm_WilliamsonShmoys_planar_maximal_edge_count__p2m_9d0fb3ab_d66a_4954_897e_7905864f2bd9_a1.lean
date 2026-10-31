-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- name    : WilliamsonShmoys.planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:27.932227+00:00
-- url     : https://prove2.me/theorems/b04ea11c-8c6a-4b93-ac52-6786df466eaf
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A finite simple graph on at least three vertices that has a crossing-free drawing and is maximal among planar supergraphs on the same vertex type has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count__p2m_9d0fb3ab_d66a_4954_897e_7905864f2bd9_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hPlanar : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
