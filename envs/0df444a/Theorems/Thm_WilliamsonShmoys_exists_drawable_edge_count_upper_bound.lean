-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_edge_count_upper_bound
-- name    : WilliamsonShmoys.exists_drawable_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:35:24.32124+00:00
-- url     : https://prove2.me/theorems/61fad30f-1c0d-42a8-8b33-c7fc5ada34ed
-- title:
--   Planar edge count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
