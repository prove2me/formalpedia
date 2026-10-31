-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:12:16.136532+00:00
-- url     : https://prove2.me/theorems/39b19b3a-0192-4155-8e70-5ad145d3ea40
-- title:
--   Planar edge upper bound
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_81f5bc0c_f9d2_498a_8992_3186a8a606eb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
