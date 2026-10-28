-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_with_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_supergraph_with_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:11:50.952417+00:00
-- url     : https://prove2.me/theorems/cc20b238-bb42-45fd-bcfd-09a78f307735
-- title:
--   Augment a drawable graph to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_with_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
