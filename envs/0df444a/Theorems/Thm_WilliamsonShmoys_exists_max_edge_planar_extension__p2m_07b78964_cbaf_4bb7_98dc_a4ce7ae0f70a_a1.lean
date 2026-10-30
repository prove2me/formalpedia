-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- name    : WilliamsonShmoys.exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:57:09.299039+00:00
-- url     : https://prove2.me/theorems/29782dd3-0f1b-4e01-b9eb-fb2f369524d3
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every finite planar graph has a planar supergraph on the same vertex type whose edge count is at least the original graph’s and at least that of every other planar supergraph of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_max_edge_planar_extension__p2m_07b78964_cbaf_4bb7_98dc_a4ce7ae0f70a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard) := by sorry
