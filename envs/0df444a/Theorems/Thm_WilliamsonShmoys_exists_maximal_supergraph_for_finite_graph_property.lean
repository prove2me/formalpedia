-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_graph_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:05:50.957908+00:00
-- url     : https://prove2.me/theorems/a6672a0d-600a-491d-9baa-bf9a54710ef4
-- title:
--   Maximal supergraphs for properties on finite graphs
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under graph inclusion. This child removes the finite-choice argument from the target: enumerate the finite type of graphs, restrict to those containing the given graph and satisfying the property, and maximize the number of edges. The candidate set is nonempty because it contains the given graph; if a qualifying graph contains the maximizer, maximal edge count and inclusion force the reverse inclusion. This argument handles empty vertex and edge sets as well. The remaining core obligation is formalizing that finite maximization and the implication from equal finite edge cardinalities plus inclusion to reverse graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_graph_property
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (Y : SimpleGraph V) (hY : P Y) :
    ∃ Z : SimpleGraph V, Y ≤ Z ∧ P Z ∧
      ∀ W : SimpleGraph V, Z ≤ W → P W → W ≤ Z := by
  sorry
