-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_free_arc
-- name    : WilliamsonShmoys.planar_drawing_extend_free_arc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:16:27.493103+00:00
-- url     : https://prove2.me/theorems/d1db9182-e574-4407-abb5-cdc11d079e5a
-- title:
--   Extend a planar drawing along a free arc
-- statement:
--   Given explicit drawing data and a simple arc from u to v whose interior avoids every vertex and whose intersections with existing edge arcs occur only at endpoints, extend the graph by the edge {u,v} and retain a planar drawing, assuming that edge was absent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extend_free_arc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (u v : V) (hNotAdj : ¬ G.Adj u v)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
