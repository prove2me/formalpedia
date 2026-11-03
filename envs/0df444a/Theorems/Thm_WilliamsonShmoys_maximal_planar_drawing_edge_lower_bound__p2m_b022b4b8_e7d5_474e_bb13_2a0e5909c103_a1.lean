-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:45:31.761659+00:00
-- url     : https://prove2.me/theorems/0c026a9e-319c-4e6b-bdab-a1e6ad38d237
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   If a graph on at least three vertices has the specified planar drawing and no drawable supergraph on those vertices properly extends it, then it has at least 3|V|−6 edges. The standard route is to show maximality forces a triangulated embedding and count faces and edge incidences using Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b022b4b8_e7d5_474e_bb13_2a0e5909c103_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     3 * Fintype.card V - 6 <= K.edgeFinset.card) := by sorry
