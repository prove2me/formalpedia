-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_edge_bounds
-- name    : WilliamsonShmoys.planar_drawing_component_edge_bounds
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:30:32.776246+00:00
-- url     : https://prove2.me/theorems/7a48d395-b31e-4d78-ab9f-7f4ccc82d93a
-- title:
--   Euler edge bound on each connected component of a drawable graph
-- statement:
--   Each connected component of a graph with a crossing-free drawing either has fewer than three vertices and at most one edge, or satisfies the planar Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_drawing_component_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∀ c : U.ConnectedComponent,
      (Nat.card c < 3 ∧ c.toSimpleGraph.edgeSet.ncard ≤ 1) ∨
      (3 ≤ Nat.card c ∧
        c.toSimpleGraph.edgeSet.ncard + 6 ≤ 3 * Nat.card c) := by sorry
