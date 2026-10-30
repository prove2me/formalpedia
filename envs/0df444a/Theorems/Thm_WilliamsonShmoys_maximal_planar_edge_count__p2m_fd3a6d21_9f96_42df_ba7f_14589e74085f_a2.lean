-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:00:31.170875+00:00
-- url     : https://prove2.me/theorems/37c28fdb-a658-40e3-b030-60d915d37051
-- title:
--   Count the edges of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable finite simple graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_fd3a6d21_9f96_42df_ba7f_14589e74085f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H →
      Set.Subset K.edgeSet H.edgeSet →
      Set.Subset H.edgeSet K.edgeSet)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
