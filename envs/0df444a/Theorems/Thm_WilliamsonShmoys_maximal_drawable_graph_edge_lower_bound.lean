-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:50:11.135828+00:00
-- url     : https://prove2.me/theorems/1176f3f1-fbd8-4a0d-b66b-36bdd6543cc3
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable edge supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : ∀ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet →
      HasPlanarDrawingOn M → M.edgeSet = G.edgeSet) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry
