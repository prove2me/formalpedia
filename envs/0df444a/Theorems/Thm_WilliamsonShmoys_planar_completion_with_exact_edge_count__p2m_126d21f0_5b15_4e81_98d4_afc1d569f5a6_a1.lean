-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1
-- name    : WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:39:16.645197+00:00
-- url     : https://prove2.me/theorems/611c5e27-b46d-4fae-a676-63177eb6dd3b
-- title:
--   Completion of a drawable graph to a triangulation-sized supergraph
-- statement:
--   Every graph with the specified crossing-free drawing on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_with_exact_edge_count__p2m_126d21f0_5b15_4e81_98d4_afc1d569f5a6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       K.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
