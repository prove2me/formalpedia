-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:26.574376+00:00
-- url     : https://prove2.me/theorems/319863c5-d9cf-422f-8cc1-e579df5fd0de
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_3a1649bb_b908_4400_8c80_435b14739a2c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ L : SimpleGraph V,
      M.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      M.edgeSet = L.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
