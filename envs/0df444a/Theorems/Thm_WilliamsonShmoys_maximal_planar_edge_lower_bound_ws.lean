-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_ws
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_ws
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:37:18.565902+00:00
-- url     : https://prove2.me/theorems/2e7d00b8-5974-490e-9303-c9772b5df7af
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A finite planar simple graph that is inclusion-maximal among drawable graphs on its vertex set, with at least three vertices, has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_ws {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : 3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
