-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:45:14.616144+00:00
-- url     : https://prove2.me/theorems/1c9f52e8-ade1-4d42-a472-428ee1f22185
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3n−6 edges. This supplies the target’s upper bound; a proof can use Euler’s formula after connecting components in the drawing and counting at least three edge occurrences per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_from_drawing__p2m_9b9fadfe_20c3_484e_b25c_37db0802734a_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) : S.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
