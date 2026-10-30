-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_completion_lower_bound
-- name    : WilliamsonShmoys.planar_graph_edge_completion_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:39:49.359483+00:00
-- url     : https://prove2.me/theorems/72308e48-e747-4e51-91df-6580f74849c1
-- title:
--   Planar graphs admit a dense planar completion
-- statement:
--   Every planar graph on a finite ordered vertex type with at least three vertices has a planar supergraph on the same vertex type with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_completion_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
