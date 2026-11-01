-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:07.15288+00:00
-- url     : https://prove2.me/theorems/88aeae11-6627-4561-98a0-139448671fc8
-- title:
--   An inclusion-maximal planar drawing has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges. The face-triangulation and Euler-counting argument is the core geometric work remaining after the parent’s maximal extension step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangulation_edge_count__p2m_64226b9d_e479_429e_9ec8_cb1b67946ff3_a3
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
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
