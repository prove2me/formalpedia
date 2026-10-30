-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:33.300337+00:00
-- url     : https://prove2.me/theorems/bfc81ce3-c50f-433a-ae04-d243cae0dc3b
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has at most 3|V|−6 edges. The size hypothesis is the boundary condition for the planar Euler bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_76a86dc1_411a_4f86_8755_ab6ac02ce22d_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
