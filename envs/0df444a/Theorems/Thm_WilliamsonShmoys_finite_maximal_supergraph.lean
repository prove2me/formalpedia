-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph
-- name    : WilliamsonShmoys.finite_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:22:50.328807+00:00
-- url     : https://prove2.me/theorems/7f7c9d74-2973-465a-b0d8-ce8b470e649e
-- title:
--   Finite maximal extension under a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite vertex type, a graph satisfying the predicate has a supergraph satisfying it that is maximal under adjacency inclusion; the extension has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      P H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        P K → K = H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
