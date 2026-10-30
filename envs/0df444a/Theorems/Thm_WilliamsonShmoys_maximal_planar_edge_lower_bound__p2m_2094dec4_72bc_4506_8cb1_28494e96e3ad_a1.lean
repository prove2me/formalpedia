-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- name    : WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:01.897609+00:00
-- url     : https://prove2.me/theorems/c0a0923f-80ba-42b7-94c8-2839ea9a76f3
-- title:
--   Lower bound for a connected maximal planar graph
-- statement:
--   This removes the lower-bound half of the target. A proof route is to obtain the plane embedding and its faces from the given drawing; use connectedness and maximality to show that every face is triangular, since a face with a longer boundary admits a diagonal that preserves planarity and strictly enlarges the graph; then combine Euler’s formula with edge-face incidence counting. The hypotheses retain the vertex lower bound, connectedness, the original drawing, and maximality, including the small boundary case of three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2094dec4_72bc_4506_8cb1_28494e96e3ad_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
