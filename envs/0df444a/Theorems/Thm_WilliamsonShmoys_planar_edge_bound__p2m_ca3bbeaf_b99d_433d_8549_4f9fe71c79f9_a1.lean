-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:35:13.569144+00:00
-- url     : https://prove2.me/theorems/f09f3524-c856-4011-8ae0-deaee3a01b51
-- title:
--   Planar simple graphs satisfy the Euler edge bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_edge_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
