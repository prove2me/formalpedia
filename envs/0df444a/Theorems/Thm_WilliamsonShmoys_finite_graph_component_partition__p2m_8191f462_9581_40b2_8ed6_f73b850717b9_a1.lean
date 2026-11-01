-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- name    : WilliamsonShmoys.finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:32:56.579999+00:00
-- url     : https://prove2.me/theorems/541f4d18-a1f1-4871-8c63-71c1d558c1ee
-- title:
--   Finite graph partition into connected components
-- statement:
--   Partition the vertices of any finite graph into disjoint parts covering all vertices, so the endpoints of each edge lie in a common part. This supplies the graph-specific component construction while leaving edge counting to a separate lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.finite_graph_component_partition__p2m_8191f462_9581_40b2_8ed6_f73b850717b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) :
    ∃ C : V → Finset V,
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C = Finset.univ) ∧
      (∀ u v, L.Adj u v → ∃ i, u ∈ C i ∧ v ∈ C i) := by sorry
