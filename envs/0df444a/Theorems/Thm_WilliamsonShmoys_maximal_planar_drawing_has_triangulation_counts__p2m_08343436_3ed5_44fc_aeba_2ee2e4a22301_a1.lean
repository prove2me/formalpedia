-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:29:47.31189+00:00
-- url     : https://prove2.me/theorems/80d3c120-40ab-4263-83fa-69737aacfbab
-- title:
--   Euler and face-incidence counts for maximal planar drawings
-- statement:
--   For a maximal drawable graph on at least three vertices, there is a number of faces f such that Euler’s formula gives |V| + f = |E| + 2 and triangular face-edge incidence gives 3f = 2|E|. Combining these yields the required edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_counts__p2m_08343436_3ed5_44fc_aeba_2ee2e4a22301_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    exists f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f = 2 * K.edgeSet.ncard := by sorry
