-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_b5197173
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_b5197173
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:48:16.544985+00:00
-- url     : https://prove2.me/theorems/a6ea0fa9-2a5f-4d19-9313-d39b14143db4
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no proper drawable supergraph has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_b5197173
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ P : SimpleGraph V, M <= P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by sorry
