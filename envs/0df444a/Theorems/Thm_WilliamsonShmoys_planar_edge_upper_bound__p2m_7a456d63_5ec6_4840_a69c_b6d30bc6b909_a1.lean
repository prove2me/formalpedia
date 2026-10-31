-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:27.39663+00:00
-- url     : https://prove2.me/theorems/d61810ad-72dd-44a6-9339-c836b4de23da
-- title:
--   Planar edge upper bound from a drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
