-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:37:30.842291+00:00
-- url     : https://prove2.me/theorems/d41641eb-86db-4b4e-b9d1-2259e7f78f1b
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal simple planar graph on a finite vertex type with at least three vertices has exactly 3n−6 edges. The lower bound is needed for the triangulation and Euler edge-count argument; it includes the three-vertex triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_for_triangulation_1e14dc85_fe67_4e30_934e_c619828dd605
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDrawing : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMaximal : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by
  sorry
