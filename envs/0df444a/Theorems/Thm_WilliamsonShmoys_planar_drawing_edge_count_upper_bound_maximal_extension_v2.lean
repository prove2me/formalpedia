-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_maximal_extension_v2
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_maximal_extension_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:23:27.203693+00:00
-- url     : https://prove2.me/theorems/4f1e396a-2220-43c2-9f54-bad3c2324baf
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Any drawable simple graph on a finite vertex type is contained in an inclusion-maximal drawable simple graph on the same vertex type. This isolates the finite maximality argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_maximal_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
