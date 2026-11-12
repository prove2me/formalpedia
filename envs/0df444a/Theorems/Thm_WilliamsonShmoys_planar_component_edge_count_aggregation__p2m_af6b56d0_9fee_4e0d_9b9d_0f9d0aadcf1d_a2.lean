-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- name    : WilliamsonShmoys.planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:52.680016+00:00
-- url     : https://prove2.me/theorems/98235c6f-660a-40d6-a6c4-218b22f2584f
-- title:
--   Aggregate edge bounds across planar components
-- statement:
--   Combine local connected planar bounds into a bound for the whole graph, given a partition whose parts contain every edge. For parts of size at least three, use `hlarge`; for size one the induced graph has no edges, and for size two simplicity allows at most one edge. Sum these counts over the disjoint partition and use the total vertex count of at least three. This leaves finite-set edge counting and arithmetic as a separate reusable obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_edge_count_aggregation__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (parts : Finset (Finset V))
    (hcover : ∀ v, ∃ C, C ∈ parts ∧ v ∈ C)
    (hnonempty : ∀ C, C ∈ parts → C.Nonempty)
    (hdisjoint : ∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D)
    (hadj : ∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C)
    (hconn : ∀ C, C ∈ parts → (M.induce (C : Set V)).Connected)
    (hdraw : ∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V)))
    (hlarge : ∀ C, C ∈ parts → 3 ≤ Fintype.card {x : V // x ∈ C} →
      (M.induce (C : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {x : V // x ∈ C})
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
