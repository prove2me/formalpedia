-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_efc6e0da
-- name    : WilliamsonShmoys.planar_edge_count_completion_efc6e0da
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:08:31.290332+00:00
-- url     : https://prove2.me/theorems/cc33e39e-4da4-4485-9d7d-dd249657fee8
-- title:
--   Planar completion with the exact edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices extends, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_completion_efc6e0da
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ J : SimpleGraph V,
      G ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
