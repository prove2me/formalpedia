-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_euler_edge_count_95ea5390
-- name    : WilliamsonShmoys.planar_completion_with_exact_euler_edge_count_95ea5390
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:59:19.520414+00:00
-- url     : https://prove2.me/theorems/1dc633c7-70a8-4274-883e-7335c1c0b3c4
-- title:
--   A planar drawing has a completion with the Euler edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_completion_with_exact_euler_edge_count_95ea5390
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
