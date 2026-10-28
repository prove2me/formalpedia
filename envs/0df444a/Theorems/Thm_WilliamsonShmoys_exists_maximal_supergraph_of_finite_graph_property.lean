-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_graph_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:04:16.529421+00:00
-- url     : https://prove2.me/theorems/ca127589-c778-48e0-ae65-6d63f644a788
-- title:
--   Finite maximal supergraph for a hereditary graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property that is preserved when edges are removed has a property-satisfying maximal supergraph. The extension contains at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_graph_property
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ A B : SimpleGraph V, A ≤ B → P B → P A)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      P H ∧
      ∀ H' : SimpleGraph V, H < H' → ¬ P H' := by sorry
