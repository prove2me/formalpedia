-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- name    : WilliamsonShmoys.inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:01:37.741206+00:00
-- url     : https://prove2.me/theorems/9a9e5c69-ecec-470e-a422-cdf4baf4a7b3
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.inclusionMaximalPlanarSupergraph_has_maxEdges__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (J : SimpleGraph V) (_ : DecidableRel J.Adj),
      H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    3 * Fintype.card V - 6 = H.edgeFinset.card := by sorry
