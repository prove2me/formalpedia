-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_strict_augmentation_below_bound
-- name    : WilliamsonShmoys.planar_drawable_strict_augmentation_below_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:47:48.879276+00:00
-- url     : https://prove2.me/theorems/330723eb-06ad-4333-b931-f75a2e03f575
-- title:
--   A drawable graph below the planar bound admits a strict drawable augmentation
-- statement:
--   If a finite drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_strict_augmentation_below_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hV : 3 <= Fintype.card V)
    (hlt : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V,
      (∀ {u v}, R.Adj u v → S.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧ S ≠ R := by sorry
