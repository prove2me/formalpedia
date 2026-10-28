-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_partition_edge_bound
-- name    : WilliamsonShmoys.finite_partition_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:46:03.784763+00:00
-- url     : https://prove2.me/theorems/c6160f6c-0be3-4eb1-8ecc-02dcb323b49b
-- title:
--   Assemble an edge bound across a vertex partition
-- statement:
--   For a finite partition of the vertices that contains both endpoints of every edge, local bounds on large blocks and a half-vertex edge budget on small blocks imply the global edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_partition_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (P : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! S : Finset V, S ∈ P ∧ v ∈ S)
    (hedgeInternal : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S : Finset V, S ∈ P ∧ u ∈ S ∧ v ∈ S)
    (hlarge : ∀ S : Finset V, S ∈ P → 3 ≤ S.card →
      (G.induce (S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card)
    (hsmall : ∀ S : Finset V, S ∈ P → S.card < 3 →
      2 * (G.induce (S : Set V)).edgeSet.ncard ≤ S.card) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
