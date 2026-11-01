-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- name    : WilliamsonShmoys.planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:54.395322+00:00
-- url     : https://prove2.me/theorems/e7b88b3e-57d2-4e16-879b-dc797a764fee
-- title:
--   Component partition and local planar edge bounds
-- statement:
--   A graph with the supplied planar drawing can be partitioned into disjoint vertex pieces covering all vertices, with every edge counted exactly once inside a piece. Each piece of size at least three has the planar `3m−6` edge bound; pieces of size two have at most one edge, and pieces of size at most one have none.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.planar_drawing_component_partition_edge_bounds__p2m_fd05939c_3060_4687_b686_08bcaa4f6cdd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard) ∧
      (∀ i,
        if 3 ≤ (C i).card then
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 3 * (C i).card - 6
        else if 2 ≤ (C i).card then
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard ≤ 1
        else
          (L.induce (fun v => v ∈ C i)).edgeSet.ncard = 0) := by sorry
