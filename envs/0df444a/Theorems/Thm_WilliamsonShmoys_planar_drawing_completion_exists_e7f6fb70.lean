-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exists_e7f6fb70
-- name    : WilliamsonShmoys.planar_drawing_completion_exists_e7f6fb70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:11:46.344678+00:00
-- url     : https://prove2.me/theorems/c0495696-a1b5-4600-ac91-4d47eb1a0df5
-- title:
--   A maximal planar completion exists
-- statement:
--   Every finite drawn graph has a drawing-preserving supergraph on the same vertices that is maximal under edge addition and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion_exists_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, Y.Adj u v → H.Adj u v) ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ ⦃u v⦄, K.Adj u v → H.Adj u v) := by sorry
