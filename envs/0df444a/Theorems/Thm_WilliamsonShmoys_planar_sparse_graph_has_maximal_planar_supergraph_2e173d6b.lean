-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_sparse_graph_has_maximal_planar_supergraph_2e173d6b
-- name    : WilliamsonShmoys.planar_sparse_graph_has_maximal_planar_supergraph_2e173d6b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:34:43.157426+00:00
-- url     : https://prove2.me/theorems/ac91856a-8214-4222-8e5b-855e95d2c043
-- title:
--   Every finite planar graph has a maximal planar supergraph
-- statement:
--   Every finite graph with a crossing-free drawing is contained in an inclusion-maximal graph with a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_sparse_graph_has_maximal_planar_supergraph_2e173d6b
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
