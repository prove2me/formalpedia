-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:12:31.06183+00:00
-- url     : https://prove2.me/theorems/017fa3bd-a11a-42f0-a60e-fe3ebb157a5f
-- title:
--   Exact edge count for an edge-maximal planar drawing
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_e34a2546_c833_4430_ac36_3fbd756a8832_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
