-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:54.527013+00:00
-- url     : https://prove2.me/theorems/fbd4abfa-95e6-415e-91e9-eb5757f71c9a
-- title:
--   Exact edge count for a maximal drawable connected graph
-- statement:
--   An inclusion-maximal drawable connected simple graph on at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hConn : ∀ u v, Relation.ReflTransGen K.Adj u v)
    (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
