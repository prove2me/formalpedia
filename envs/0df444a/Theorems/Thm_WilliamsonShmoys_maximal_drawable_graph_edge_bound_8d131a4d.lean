-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_8d131a4d
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_bound_8d131a4d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:31:06.126613+00:00
-- url     : https://prove2.me/theorems/b748e320-f0ef-4067-9bf7-d7863694a40f
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph that is inclusion-maximal among drawable graphs on the same finite vertex type, with at least three vertices, has at most 3|V|−6 edges. The proof route uses the maximal planar structure, triangular-face incidence counting, and Euler’s formula. The lower bound on the vertex count is essential; with three vertices, maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_bound_8d131a4d
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, H ≤ M → HasPlanarDrawingOn M → M ≤ H) :
    (H.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
