-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:29:37.185587+00:00
-- url     : https://prove2.me/theorems/7af0eddf-6827-49cb-9eed-42a53389680e
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_triangulation {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧ 3 * Fintype.card V = J.edgeSet.ncard + 6 := by sorry
