-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:22:42.117601+00:00
-- url     : https://prove2.me/theorems/dbcd4af9-e055-47f7-910a-a01842a93823
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A connected simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_6cac0be3_cdae_42f1_a688_5a8b1965052e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hPlanar : HasPlanarDrawingOn H)
    (hConn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
