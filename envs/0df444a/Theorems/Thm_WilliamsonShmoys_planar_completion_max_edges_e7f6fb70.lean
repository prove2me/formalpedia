-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_max_edges_e7f6fb70
-- name    : WilliamsonShmoys.planar_completion_max_edges_e7f6fb70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:35:27.772255+00:00
-- url     : https://prove2.me/theorems/9a93d45d-276b-45b8-89eb-f62ab7a73e9b
-- title:
--   Every finite planar drawing extends to a triangulation
-- statement:
--   Any finite simple graph with a crossing-free drawing on at least three fixed vertices is a subgraph of a graph on the same vertex set that also has a crossing-free drawing and exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_max_edges_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
