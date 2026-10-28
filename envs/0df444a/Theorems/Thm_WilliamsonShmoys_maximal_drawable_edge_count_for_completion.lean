-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_completion
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:07:12.302136+00:00
-- url     : https://prove2.me/theorems/0e150c24-7b44-4049-9d9d-8ca4cc623f98
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on those vertices has exactly three times the vertex count minus six edges. This removes the geometric and Euler-counting obligation from the parent. A proof route is to derive from maximality that the drawing is connected and every face is triangular, then use Euler’s formula and count face-edge incidences; the cited textbook theorem is relevant, though its proof text was unavailable for direct checking.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMdraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
