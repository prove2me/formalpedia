-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:37:47.849635+00:00
-- url     : https://prove2.me/theorems/0df19a3a-91dd-4e4b-942c-e5b79d23d807
-- title:
--   Maximality forces the triangulation edge lower bound
-- statement:
--   An inclusion-maximal graph with the specified crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_88aeae11_6627_4561_98a0_139448671fc8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      letI : DecidableRel G.Adj := dG
      letI : DecidableRel K.Adj := dK
      HasPlanarDrawingOn K →
      G.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset = G.edgeFinset) :
    letI : DecidableRel G.Adj := dG
    3 * Fintype.card V - 6 ≤ G.edgeFinset.card := by sorry
