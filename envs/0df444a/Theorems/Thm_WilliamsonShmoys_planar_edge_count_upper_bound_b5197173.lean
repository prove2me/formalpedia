-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_b5197173
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_b5197173
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:34:29.873601+00:00
-- url     : https://prove2.me/theorems/5e257038-8d44-4dde-b570-f331931903f6
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Every graph satisfying the supplied crossing-free drawing predicate, on at least three vertices, has at most 3n - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_b5197173
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
