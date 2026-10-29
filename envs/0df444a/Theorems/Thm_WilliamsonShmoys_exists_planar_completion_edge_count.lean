-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_completion_edge_count
-- name    : WilliamsonShmoys.exists_planar_completion_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:51:48.763861+00:00
-- url     : https://prove2.me/theorems/271d2eb8-0883-4afb-88e9-925bc682e12d
-- title:
--   Planar completion attains the maximal edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_completion_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
