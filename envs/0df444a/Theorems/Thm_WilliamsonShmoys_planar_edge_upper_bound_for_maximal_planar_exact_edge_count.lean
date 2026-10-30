-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_maximal_planar_exact_edge_count
-- name    : WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:15:06.537788+00:00
-- url     : https://prove2.me/theorems/aeaff05e-5026-4427-9c46-0128a7dba5bd
-- title:
--   Planar edge upper bound for the maximal planar edge count theorem
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges, whether or not it is connected. This is the Euler-formula upper bound used in the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_for_maximal_planar_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
