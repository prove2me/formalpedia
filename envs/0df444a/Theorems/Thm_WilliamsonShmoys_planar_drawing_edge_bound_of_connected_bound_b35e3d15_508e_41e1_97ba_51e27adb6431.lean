-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_connected_bound_b35e3d15_508e_41e1_97ba_51e27adb6431
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound_b35e3d15_508e_41e1_97ba_51e27adb6431
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:30:54.751329+00:00
-- url     : https://prove2.me/theorems/ff9c213e-8518-4985-b6fc-87d0d36c0258
-- title:
--   Assemble the planar edge bound from connected cases
-- statement:
--   If every connected finite simple graph with at least three vertices satisfies the planar drawing edge bound, then every finite simple graph with at least three vertices satisfies it. Restrict the drawing to connected components, handle components of size one or two directly, and combine the bounds; the total size hypothesis supplies the required slack of six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_of_connected_bound_b35e3d15_508e_41e1_97ba_51e27adb6431
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (K : SimpleGraph W),
      3 ≤ Fintype.card W → K.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
