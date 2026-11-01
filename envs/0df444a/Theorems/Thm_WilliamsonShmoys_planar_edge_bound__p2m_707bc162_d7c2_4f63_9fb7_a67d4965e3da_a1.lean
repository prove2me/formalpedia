-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:09.01414+00:00
-- url     : https://prove2.me/theorems/9af9a27b-506f-4127-9aee-1c90d198b1ff
-- title:
--   Planar simple graph edge bound
-- statement:
--   Every drawable simple graph on at least three finite vertices has at most `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_707bc162_d7c2_4f63_9fb7_a67d4965e3da_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) (hn : 3 ≤ Fintype.card V) : (letI : DecidableRel K.Adj := dK; K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
