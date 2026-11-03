-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:09:27.063206+00:00
-- url     : https://prove2.me/theorems/1508a319-0bdf-43a6-9c8f-5ec7d4360d47
-- title:
--   Edge bound for a finite simply drawn planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing as defined by HasPlanarDrawingOn has at most three times its number of vertices minus three edges, with subtraction interpreted in Nat. This includes zero, one, and two vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound__p2m_278b0a4b_e4b3_4f5b_934c_d513e35b19a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel _
    G.edgeFinset.card ≤ 3 * Fintype.card V - 3 := by sorry
