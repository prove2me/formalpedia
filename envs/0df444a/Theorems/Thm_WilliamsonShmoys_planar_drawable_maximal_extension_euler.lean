-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_euler
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:19:37.782988+00:00
-- url     : https://prove2.me/theorems/0bddf106-34d7-477e-9a27-7b669d8814d5
-- title:
--   Drawable supergraph with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_extension_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      (∀ {u v}, Q.Adj u v → R.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
