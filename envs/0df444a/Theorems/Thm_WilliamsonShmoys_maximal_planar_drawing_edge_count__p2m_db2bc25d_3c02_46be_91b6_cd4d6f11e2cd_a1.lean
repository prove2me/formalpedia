-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:36.352844+00:00
-- url     : https://prove2.me/theorems/0a0c7b94-7c6b-416a-9a27-7e1438879d42
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal under drawable supergraph inclusion has exactly 3|V|−6 edges. The lower bound on the vertex count is essential to this formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_db2bc25d_3c02_46be_91b6_cd4d6f11e2cd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hR : HasPlanarDrawingOn R)
    (hMax : ∀ H : SimpleGraph V, R ≤ H → HasPlanarDrawingOn H → H = R) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     3 * Fintype.card V = R.edgeFinset.card + 6) := by sorry
