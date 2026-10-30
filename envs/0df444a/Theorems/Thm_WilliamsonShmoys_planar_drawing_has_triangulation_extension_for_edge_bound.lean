-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension_for_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:45:04.364419+00:00
-- url     : https://prove2.me/theorems/c92dc612-2624-400b-9b58-2c4c86f5886c
-- title:
--   Extend a planar drawing to a triangulation with the Euler edge count
-- statement:
--   Any finite planar graph on at least three vertices has a planar supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulation_extension_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
