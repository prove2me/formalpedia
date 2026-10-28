-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_euler_extension
-- name    : WilliamsonShmoys.maximal_planar_edge_count_euler_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:21:11.054969+00:00
-- url     : https://prove2.me/theorems/179e6262-6403-4b0f-8e54-7f52a8498b09
-- title:
--   Triangulated planar extension on the same vertex type
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable extension on the same vertex type whose edge count is 3|V|−6. This is the triangulation-and-Euler step; the parent uses maximality to show the extension has no additional edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_euler_extension {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hCard : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
