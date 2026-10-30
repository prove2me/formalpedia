-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:04.76504+00:00
-- url     : https://prove2.me/theorems/06103664-1c63-47e0-9ef5-c7865ee277ce
-- title:
--   A maximal planar graph has the Euler edge count
-- statement:
--   A graph on at least three vertices that admits the supplied crossing-free drawing and is maximal under edge inclusion among graphs admitting such a drawing has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_has_euler_edge_count__p2m_80e34e39_9312_4353_9ec3_c3ff17c125fa_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hMax : ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet = H.edgeSet) : H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
