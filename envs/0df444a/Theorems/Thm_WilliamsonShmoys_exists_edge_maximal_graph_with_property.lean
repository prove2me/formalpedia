-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_graph_with_property
-- name    : WilliamsonShmoys.exists_edge_maximal_graph_with_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:13:46.943326+00:00
-- url     : https://prove2.me/theorems/2ceaa0eb-0d2a-4b6a-9b48-6d9ec9b085e7
-- title:
--   Finite edge maximality for a graph property
-- statement:
--   For any property P of simple graphs on a finite linearly ordered vertex type, if J has P, then J has a P supergraph that is maximal among P supergraphs under edge-set inclusion. The candidate family is nonempty because it contains J. Since there are finitely many simple graphs, choose a candidate with maximum edge count. Any strict P supergraph would have more edges and contradict maximality of that count. This removes the finite maximizer argument from the target; the target follows by taking P to be `WilliamsonShmoys.HasPlanarDrawingOn` and applying the result to hJ. The remaining core obligation is to formalize this finite maximum argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_graph_with_property
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P J) :
    ∃ K : SimpleGraph V,
      J.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        P L →
        L.edgeSet = K.edgeSet := by
  sorry
