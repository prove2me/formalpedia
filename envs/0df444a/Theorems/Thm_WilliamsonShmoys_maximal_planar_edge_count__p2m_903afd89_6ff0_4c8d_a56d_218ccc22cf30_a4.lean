-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:37.191924+00:00
-- url     : https://prove2.me/theorems/97520866-02f5-403f-95e4-783b62094e18
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has exactly 3|V|−6 edges. The proof route is to show maximality forces connectedness and triangular faces, then use Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_903afd89_6ff0_4c8d_a56d_218ccc22cf30_a4 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ Q : SimpleGraph V, N ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ N) : N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
