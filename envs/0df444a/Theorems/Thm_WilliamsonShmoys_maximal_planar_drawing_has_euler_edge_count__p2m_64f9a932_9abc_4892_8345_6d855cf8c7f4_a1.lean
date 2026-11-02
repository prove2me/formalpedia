-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:38:14.811533+00:00
-- url     : https://prove2.me/theorems/b022b4b8-e7d5-474e-bb13-2a0e5909c103
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   For a graph on at least three finite linearly ordered vertices, if it has the supplied planar drawing and no drawable supergraph on those vertices properly extends it, then its edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_64f9a932_9abc_4892_8345_6d855cf8c7f4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     3 * Fintype.card V - 6 = K.edgeFinset.card) := by
  sorry
