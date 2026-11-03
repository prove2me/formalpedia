-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:43.237025+00:00
-- url     : https://prove2.me/theorems/3ab951ac-7c5a-45ca-9684-f3fed84a5e33
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3n − 6 edges. The independent proof route is to show maximality forces a connected embedding with triangular faces, then apply Euler’s formula; for three vertices the resulting bound is three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_d6b9112d_6e11_42e8_8b1b_3d46cf1b698c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
