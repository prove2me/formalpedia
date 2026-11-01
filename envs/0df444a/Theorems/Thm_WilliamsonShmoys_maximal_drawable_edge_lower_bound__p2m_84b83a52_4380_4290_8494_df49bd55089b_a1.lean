-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:44.918186+00:00
-- url     : https://prove2.me/theorems/4adfb18f-d05e-40a4-90b7-ec7e79d3a996
-- title:
--   Edge lower bound for an edge-maximal drawable graph
-- statement:
--   An edge-maximal finite drawable simple graph on at least three vertices has at least 3n−6 edges; maximality rules out nontriangular faces in a planar embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
