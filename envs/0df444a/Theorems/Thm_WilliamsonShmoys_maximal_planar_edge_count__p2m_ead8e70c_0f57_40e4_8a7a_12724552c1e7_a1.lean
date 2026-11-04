-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:18.779765+00:00
-- url     : https://prove2.me/theorems/1cbebd7a-cbfe-40cb-8e61-899ac9ec9081
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal simple graph admitting the supplied crossing-free drawing, on at least three vertices, has exactly 3|V| − 6 edges. This removes the topological edge-count argument from the parent, leaving the parent to construct the face-count witness and discharge the two arithmetic equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_ead8e70c_0f57_40e4_8a7a_12724552c1e7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
