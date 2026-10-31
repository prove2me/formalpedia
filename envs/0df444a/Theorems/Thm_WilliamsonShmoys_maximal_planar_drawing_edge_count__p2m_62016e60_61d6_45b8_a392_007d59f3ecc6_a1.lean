-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:26:17.410366+00:00
-- url     : https://prove2.me/theorems/1129f324-ed56-4814-b878-03ab3968bf96
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof must show that maximality forces triangular faces in a planar embedding, then apply Euler’s formula; when |V|=3, the asserted count is 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
