-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_data_extend_free_arc_to_supergraph
-- name    : WilliamsonShmoys.planar_drawing_data_extend_free_arc_to_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:29:20.083027+00:00
-- url     : https://prove2.me/theorems/0ad1ab07-c3b7-419b-a98b-39ebc568d81c
-- title:
--   Extend drawing data across a free arc in a supergraph
-- statement:
--   If H contains every edge of a drawn graph G and its only possible additional edge is {u,v}, then a free connecting arc from u to v extends the drawing to H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_IsPlanarDrawingData
import Definitions.Def_WilliamsonShmoys_HasFreeConnectingArc
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_data_extend_free_arc_to_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ) (u v : V)
    (hDrawing : WilliamsonShmoys.IsPlanarDrawingData G p arc)
    (hFree : WilliamsonShmoys.HasFreeConnectingArc G p arc u v)
    (hSub : G ≤ H) (hAdj : H.Adj u v)
    (hOnly : ∀ x y, H.Adj x y →
      G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
