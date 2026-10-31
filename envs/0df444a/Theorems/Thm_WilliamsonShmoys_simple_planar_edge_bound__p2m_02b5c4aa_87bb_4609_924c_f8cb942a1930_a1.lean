-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
-- name    : WilliamsonShmoys.simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:56:19.067092+00:00
-- url     : https://prove2.me/theorems/bff95f57-b2f4-4a78-b638-ad03e6867777
-- title:
--   Simple planar edge bound
-- statement:
--   For a connected simple graph with the supplied planar drawing and at least three vertices, the edge count satisfies the standard planar bound. A proof route uses Euler’s formula together with face-boundary incidence counting, treating bridges as traversed on both sides; this child isolates the quantitative estimate needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
