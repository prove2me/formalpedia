-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:21.59291+00:00
-- url     : https://prove2.me/theorems/2e383da1-b0fd-42ac-bf20-409641577930
-- title:
--   An inclusion-maximal planar drawing has exactly 3n−6 edges
-- statement:
--   A finite simple graph on at least three vertices that has a planar drawing and is maximal among drawable supergraphs on those vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_three_n_minus_six_edges__p2m_8f423dbe_14e3_49a1_828e_7cd49c2ddeb4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = K.edgeFinset.card := by sorry
