-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_f3620a14
-- name    : WilliamsonShmoys.planar_edge_bound_f3620a14
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:33:27.159587+00:00
-- url     : https://prove2.me/theorems/eb9e91c8-3528-4841-a053-6645b3466c88
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
