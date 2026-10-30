-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:06:30.799983+00:00
-- url     : https://prove2.me/theorems/71955334-b5e9-40f2-bf30-231a1d4336f4
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that has no strictly larger drawable supergraph has exactly 3|V| − 6 edges. Prove this by showing maximality makes every face triangular, then applying Euler’s formula and counting each edge along its two incident faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_3d83e52d_d7f3_4064_9901_f4d565126921
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  sorry
