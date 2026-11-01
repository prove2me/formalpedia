-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- name    : WilliamsonShmoys.edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:30.279188+00:00
-- url     : https://prove2.me/theorems/9b4fedd9-b4be-4e00-ad7f-79af66c1cf07
-- title:
--   Every edge lies in a part's filtered edge set
-- statement:
--   The filtered edge sets for all parts cover every edge. This is the coverage step of the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_partition_cover__p2m_020795f4_16c9_41f8_abc4_7a5fa01ff386_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hclosed : ∀ ⦃u v : V⦄, N.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    C.biUnion (fun s => {e ∈ N.edgeFinset | e.toFinset ⊆ s}) = N.edgeFinset := by sorry
