-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_extension
-- name    : WilliamsonShmoys.planar_drawingOn_triangulated_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:26:53.993135+00:00
-- url     : https://prove2.me/theorems/7d9031b1-895e-4936-9bea-457d986c6d3d
-- title:
--   Triangulated planar extension on the same vertices
-- statement:
--   For any drawable simple graph with at least three vertices, there is a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This general completion result supplies the maximal extension used by the target; its boundary hypothesis excludes the small cases where the edge formula need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulated_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
