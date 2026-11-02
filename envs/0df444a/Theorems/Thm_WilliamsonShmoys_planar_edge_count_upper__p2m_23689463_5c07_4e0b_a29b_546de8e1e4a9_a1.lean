-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:27.320138+00:00
-- url     : https://prove2.me/theorems/3a09bc7c-d04d-46ee-862f-d512ce00caa0
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Any finite drawable simple graph with at least three vertices has at most 3|V|−6 edges. This is the Euler upper-bound half of the target; a proof route is to establish Euler’s formula for the drawing’s faces and use that each face boundary has length at least three, accounting for disconnected drawings as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_23689463_5c07_4e0b_a29b_546de8e1e4a9_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (dL : DecidableRel L.Adj) (hL : HasPlanarDrawingOn L) (hcard : 3 <= Fintype.card V) : L.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
