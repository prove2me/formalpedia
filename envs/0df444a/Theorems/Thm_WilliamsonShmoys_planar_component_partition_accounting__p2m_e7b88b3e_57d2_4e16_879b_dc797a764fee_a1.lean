-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- name    : WilliamsonShmoys.planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:42.142126+00:00
-- url     : https://prove2.me/theorems/8191f462-9581-40b2-8ed6-f73b850717b9
-- title:
--   Connected component partition edge accounting
-- statement:
--   Every finite graph has a partition indexed by its vertices whose nonempty pieces are connected components. The pieces are disjoint and cover all vertices, and every edge is counted exactly once among the induced subgraphs on those pieces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.planar_component_partition_accounting__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (L.edgeSet.ncard = ∑ i : V, (L.induce (fun v => v ∈ C i)).edgeSet.ncard) := by sorry
