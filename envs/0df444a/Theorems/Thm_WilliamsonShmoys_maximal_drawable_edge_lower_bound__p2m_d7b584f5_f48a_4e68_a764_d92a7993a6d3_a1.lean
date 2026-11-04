-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:40:42.924784+00:00
-- url     : https://prove2.me/theorems/0abcdb56-bfcd-4329-9382-36e3242f584a
-- title:
--   Maximal drawable edge lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least three times its vertex count minus six edges. The geometric route is to show maximality leaves no nontriangular face: a missing diagonal could otherwise be drawn inside that face while preserving the existing drawing, contradicting maximality; Euler’s formula then gives the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_d7b584f5_f48a_4e68_a764_d92a7993a6d3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    letI : DecidableRel L.Adj := Classical.decRel L.Adj
    3 * Fintype.card V ≤ L.edgeFinset.card + 6 := by sorry
