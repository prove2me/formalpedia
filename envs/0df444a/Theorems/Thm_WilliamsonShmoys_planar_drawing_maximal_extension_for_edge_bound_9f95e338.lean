-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound_9f95e338
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9f95e338
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:30:19.828122+00:00
-- url     : https://prove2.me/theorems/bb9641a4-5618-4521-ad03-c55625f11445
-- title:
--   Extend a finite planar drawing to a maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing is contained in a drawn planar graph on the same vertex type that is maximal among drawn planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9f95e338
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by
  sorry
