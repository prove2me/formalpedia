-- Prove2me | Theorems.Thm_WilliamsonShmoys_partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- name    : WilliamsonShmoys.partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:12.902466+00:00
-- url     : https://prove2.me/theorems/66d9a9d7-c76c-45c0-887d-01a07c3b39fb
-- title:
--   Sharpen the local bound for each part
-- statement:
--   For each nonempty connected part, the local hypothesis implies the sharper contribution used by the target. Split on the part's cardinality: size 1 has no edges because the graph is simple; size 2 uses the local bound of 1; for size at least 3, the local bound simplifies to 3n−6. This removes the per-part arithmetic and singleton graph argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.partition_edge_local_sharp_bound__p2m_dcaefdba_b10e_4220_bda1_55f53e9c0d30_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hlocal : ∀ (s : Finset V), (K.induce (↑s : Set V)).Connected → (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card ≤ max 1 (3 * Fintype.card s - 6))) (parts : Finset (Finset V)) (s : Finset V) (hs : s ∈ parts) (hpart : s.Nonempty ∧ (K.induce (↑s : Set V)).Connected) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card ≤ if Fintype.card s ≤ 1 then 0 else if Fintype.card s = 2 then 1 else 3 * Fintype.card s - 6) := by sorry
