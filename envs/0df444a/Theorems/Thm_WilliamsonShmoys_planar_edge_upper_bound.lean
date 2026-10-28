-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound
-- name    : WilliamsonShmoys.planar_edge_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:25:26.35723+00:00
-- url     : https://prove2.me/theorems/a7c54caa-f18d-4252-a9a1-2b9c49bb9676
-- title:
--   Planar simple graphs satisfy the Euler edge upper bound
-- statement:
--   Every simply drawn planar graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
