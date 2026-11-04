-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:40.509725+00:00
-- url     : https://prove2.me/theorems/c3bfcc58-a4dc-4360-bb5c-96ba0d9daf33
-- title:
--   Maximal planar edge-count lower bound
-- statement:
--   Maximality under drawable supergraphs forces at least three times the vertex count minus six edges. For n = 3, prove this directly. For n > 3, use maximality to establish connectedness and triangular faces in the drawing, then apply Euler’s formula and the face-edge incidence count. This isolates the maximality-driven part of the argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f84a2b8d_758d_48e3_856e_f835c2dfd776_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
      3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by sorry
