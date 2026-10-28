-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_card
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_edge_card
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:46:16.680927+00:00
-- url     : https://prove2.me/theorems/9e31d0d7-bedf-4a6b-a6d6-c2c0226ce7c3
-- title:
--   Triangulated planar supergraph with exact edge count
-- statement:
--   Every finite connected graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` is contained in a planar supergraph on the same vertices with exactly `3|V| - 6` edges. Edge inclusion also gives the original graph’s edge-count inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_edge_card
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hCard : 3 ≤ Fintype.card V)
    (hConnected : S.Connected) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      S.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
