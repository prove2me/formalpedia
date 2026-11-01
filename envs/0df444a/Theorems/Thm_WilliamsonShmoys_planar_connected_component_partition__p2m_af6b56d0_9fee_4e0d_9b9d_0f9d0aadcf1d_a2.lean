-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- name    : WilliamsonShmoys.planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:27:47.831689+00:00
-- url     : https://prove2.me/theorems/5617b1c6-c5d8-46d6-8dd2-454c2352497f
-- title:
--   Partition a planar graph into drawn connected components
-- statement:
--   Represent the connected components by a finite partition of the vertex type. The statement records coverage, nonempty and pairwise disjoint parts, that every edge stays within a part, connectedness of each induced graph, and inheritance of the drawing. A proof route is to use the finite reachability equivalence classes of the graph and restrict the drawing witnesses to each class. This removes component-extraction and drawing-restriction work from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_component_partition__p2m_af6b56d0_9fee_4e0d_9b9d_0f9d0aadcf1d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ parts : Finset (Finset V),
      (∀ v, ∃ C, C ∈ parts ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → C.Nonempty) ∧
      (∀ C, C ∈ parts → ∀ D, D ∈ parts → C ≠ D → Disjoint C D) ∧
      (∀ u v, M.Adj u v → ∃ C, C ∈ parts ∧ u ∈ C ∧ v ∈ C) ∧
      (∀ C, C ∈ parts → (M.induce (C : Set V)).Connected) ∧
      (∀ C, C ∈ parts → WilliamsonShmoys.HasPlanarDrawingOn (M.induce (C : Set V))) := by
  sorry
