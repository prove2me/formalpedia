-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:58:30.593845+00:00
-- url     : https://prove2.me/theorems/b43e8544-07f5-4b4a-b232-0837cea82fd6
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   For a finite simple graph with at least three vertices, a crossing-free drawing implies that its edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_dc18341a_a219_427c_98ac_62a72970a5ea_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
