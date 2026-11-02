-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:18.766895+00:00
-- url     : https://prove2.me/theorems/11e6dfda-9f08-4732-9f3c-e6ed8e60d286
-- title:
--   Lower edge-count bound for maximal planar graphs
-- statement:
--   An edge-maximal graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V)
    [DecidableRel P.Adj] :
    3 * Fintype.card V ≤ P.edgeFinset.card + 6 := by sorry
