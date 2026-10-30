-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_e7f6fb70
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion_e7f6fb70
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:51:01.093283+00:00
-- url     : https://prove2.me/theorems/e4c4b965-c395-4c74-9d84-f710f0a10e67
-- title:
--   Triangulated planar completion of a drawn graph
-- statement:
--   Every graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has a planar supergraph on the same vertices whose edge count is exactly `3n − 6`, with edge count at least that of the original graph. The edge-count inequality and equality imply the requested bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion_e7f6fb70
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, Y.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Y.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
