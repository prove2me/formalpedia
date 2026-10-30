-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:14.121411+00:00
-- url     : https://prove2.me/theorems/d79776b6-af88-4e2b-abb0-db45e2831b04
-- title:
--   Euler bound for an edge-maximal planar graph
-- statement:
--   An edge-maximal connected graph with a crossing-free drawing on at least three vertices satisfies the planar edge bound. The remaining core is to establish from maximality that the embedding has triangular faces, then derive the result using Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_6f3d39c4_bdd3_471f_b5e3_5e407be55c6e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V),
      (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
