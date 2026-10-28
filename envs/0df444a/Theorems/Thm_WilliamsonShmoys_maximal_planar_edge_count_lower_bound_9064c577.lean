-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_9064c577
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9064c577
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:46:56.143215+00:00
-- url     : https://prove2.me/theorems/9f65e43a-d03b-4ed9-9924-d9ceac002b5a
-- title:
--   Maximality forces at least 3n−6 edges
-- statement:
--   A connected maximal simple planar graph on at least three vertices has at least \(3n-6\) edges. This removes the maximality and triangulation argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9064c577
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
