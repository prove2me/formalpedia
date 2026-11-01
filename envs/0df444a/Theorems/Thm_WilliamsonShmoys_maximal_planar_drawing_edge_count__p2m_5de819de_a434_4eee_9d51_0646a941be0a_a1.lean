-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:33.245021+00:00
-- url     : https://prove2.me/theorems/24d4a109-2712-447f-b6c6-168aeb4ef393
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_5de819de_a434_4eee_9d51_0646a941be0a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
