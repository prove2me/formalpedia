-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- name    : WilliamsonShmoys.edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:34.558322+00:00
-- url     : https://prove2.me/theorems/2f3f4607-1df5-4ab7-be24-a3aa335c2b62
-- title:
--   Filtered edge sets for distinct parts are disjoint
-- statement:
--   If a graph edge's endpoint set is contained in two parts, uniqueness of the part containing any endpoint makes those parts equal. Thus the filtered edge sets are pairwise disjoint.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_partition_disjoint__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s) :
    (C : Set (Finset V)).PairwiseDisjoint
      (fun s => {e ∈ N.edgeFinset | e.toFinset ⊆ s}) := by sorry
