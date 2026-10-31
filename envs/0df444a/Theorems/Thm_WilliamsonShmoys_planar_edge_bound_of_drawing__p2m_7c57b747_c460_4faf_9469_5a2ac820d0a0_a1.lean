-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:15:59.817403+00:00
-- url     : https://prove2.me/theorems/a893531d-2eaf-40a4-93f3-f4bc4ca725ea
-- title:
--   Euler edge bound for drawable simple graphs
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most 3|V|−6 edges. This isolates the Euler upper-bound step from the parent. A proof route is to use the drawing to establish the planar face-incidence inequalities, apply Euler’s formula componentwise or after connecting components, and count each face boundary with the simplicity and n ≥ 3 hypotheses. For n = 3 the bound is the direct maximum of three simple edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_bound_of_drawing__p2m_7c57b747_c460_4faf_9469_5a2ac820d0a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
