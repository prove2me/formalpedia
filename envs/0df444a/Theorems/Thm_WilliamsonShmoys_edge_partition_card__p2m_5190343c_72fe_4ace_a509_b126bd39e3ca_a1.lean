-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
-- name    : WilliamsonShmoys.edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:42.3502+00:00
-- url     : https://prove2.me/theorems/020795f4-16c9-41f8-abc4-7a5fa01ff386
-- title:
--   Count edges by their unique partition part
-- statement:
--   The edges of a finite graph whose endpoints lie together in a unique part are counted exactly once by summing, over the parts, the edges whose endpoints lie in that part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_partition_card__p2m_5190343c_72fe_4ace_a509_b126bd39e3ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hpartition : ∀ v : V, ∃! s : Finset V, s ∈ C ∧ v ∈ s)
    (hclosed : ∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    N.edgeFinset.card = ∑ s ∈ C, {e ∈ N.edgeFinset | e.toFinset ⊆ s}.card := by sorry
