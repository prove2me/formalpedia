-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd
-- name    : WilliamsonShmoys.planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:36:46.656967+00:00
-- url     : https://prove2.me/theorems/36d3a241-b919-419b-b1f0-bf080f70e21f
-- title:
--   Planar augmentation below the triangulation bound
-- statement:
--   A drawable simple graph on at least three vertices whose edge count is strictly below the planar bound has a proper drawable supergraph on the same vertex type. The strict inequality ensures the graph is not already a triangulation at the bound, including when there are exactly three vertices. A proof route is to augment a planar embedding by joining components and adding noncrossing edges within nontriangular faces until maximal; the resulting triangulation has the bound’s edge count, so strict sparsity ensures at least one added edge. This child contains the main augmentation and drawing-formalization obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_extension_c9504d43_439f_48f5_9c1d_7c90f019cbdd
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hSparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ ¬ K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
