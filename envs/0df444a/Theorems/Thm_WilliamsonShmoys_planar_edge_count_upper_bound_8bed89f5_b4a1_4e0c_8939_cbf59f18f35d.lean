-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:00:31.22947+00:00
-- url     : https://prove2.me/theorems/808bdc1d-58a6-4b8c-868d-ba076ae3927e
-- title:
--   Planar simple graph edge upper bound for this target
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
