-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_planar_edge_bound_retry2
-- name    : WilliamsonShmoys.maximal_drawable_planar_edge_bound_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:22:16.690528+00:00
-- url     : https://prove2.me/theorems/3485deb0-23bb-49b0-a269-fdf282e0e1eb
-- title:
--   Edge bound for maximal drawable graphs (retry 2)
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3|V|−6` edges. Maximality forces a triangulation, after which Euler’s formula yields the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_planar_edge_bound_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
