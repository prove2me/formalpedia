-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawing_has_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:02:48.782904+00:00
-- url     : https://prove2.me/theorems/199c5549-0fc8-47d6-a90e-80b934bab762
-- title:
--   Planar drawings extend to a triangulation on the same vertices
-- statement:
--   Any simply drawn planar graph on at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges. The lower bound on the vertex count is needed for the triangulation count, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
