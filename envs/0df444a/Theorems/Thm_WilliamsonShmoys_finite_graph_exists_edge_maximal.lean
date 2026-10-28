-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_exists_edge_maximal
-- name    : WilliamsonShmoys.finite_graph_exists_edge_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:29:34.160019+00:00
-- url     : https://prove2.me/theorems/db33e037-3650-4ad0-a663-5068e55aea0f
-- title:
--   Finite graph predicate has a maximal supergraph
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has a supergraph satisfying it whose edge set is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_exists_edge_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (M : SimpleGraph V) (hM : P M) :
    ∃ L : SimpleGraph V,
      P L ∧
      M.edgeSet ⊆ L.edgeSet ∧
      (∀ K : SimpleGraph V,
        P K → L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) := by sorry
