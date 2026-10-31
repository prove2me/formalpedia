-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
-- name    : WilliamsonShmoys.planar_maximal_edge_count__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:51.710305+00:00
-- url     : https://prove2.me/theorems/1c76d723-5228-4c88-9886-d3867affdb8f
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges. This isolates the triangulation and Euler-formula argument from the finite maximization step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count__p2m_54bfa514_b5d2_470b_aa39_b977e5665440_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn N)
    (hmax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) :
    3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
