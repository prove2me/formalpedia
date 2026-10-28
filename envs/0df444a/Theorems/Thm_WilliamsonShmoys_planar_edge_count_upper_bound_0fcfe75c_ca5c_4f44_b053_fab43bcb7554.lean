-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:12:26.157987+00:00
-- url     : https://prove2.me/theorems/3e188728-dce6-4c1d-a89d-3d74308da61c
-- title:
--   Planar graphs have at most 3n−6 edges
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The statement includes disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_0fcfe75c_ca5c_4f44_b053_fab43bcb7554
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hCard : 3 <= Fintype.card V) :
    Y.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
