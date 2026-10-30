-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
-- name    : WilliamsonShmoys.edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:23:18.445291+00:00
-- url     : https://prove2.me/theorems/2dc2dbd1-f809-4f7a-af37-ac9b40bde16d
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3n − 6` edges. The independent proof route is to show that maximality forces a triangulation, then count its faces using Euler’s formula. This removes the topological edge-count obligation from the parent; formalizing triangulation and Euler counting for the supplied arc-based drawing predicate remains the core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_of_maximal_drawable__p2m_df288277_9c1c_43a5_8845_caf345f4f17a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set V) [Fintype S]
    (N : SimpleGraph S)
    (hDraw : HasPlanarDrawingOn N)
    (hcard : 3 ≤ S.ncard)
    (hmax : ∀ M : SimpleGraph S, N ≤ M → HasPlanarDrawingOn M → M = N) :
    3 * S.ncard ≤ N.edgeSet.ncard + 6 := by sorry
