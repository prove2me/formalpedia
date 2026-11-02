-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:34.461417+00:00
-- url     : https://prove2.me/theorems/63f4596f-16e9-46f5-8d7e-b4c7e853b2c9
-- title:
--   Planar simple graphs satisfy the edge upper bound
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free plane drawing has at most 3n − 6 edges. This supplies the upper bound for the parent equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_0f5981a3_7974_4822_a476_e1c2ba671214_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
