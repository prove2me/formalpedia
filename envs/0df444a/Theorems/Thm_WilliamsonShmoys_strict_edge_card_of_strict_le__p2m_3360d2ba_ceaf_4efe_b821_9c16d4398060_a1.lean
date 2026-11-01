-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- name    : WilliamsonShmoys.strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:16:26.873972+00:00
-- url     : https://prove2.me/theorems/0003f7d6-bbe9-4b4a-be40-93b702988897
-- title:
--   Strict graph extension increases finite edge count
-- statement:
--   For graphs on a finite vertex type, a proper graph extension has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.strict_edge_card_of_strict_le__p2m_3360d2ba_ceaf_4efe_b821_9c16d4398060_a1 {V : Type} [Fintype V] [LinearOrder V] {G K : SimpleGraph V} (hGK : G ≤ K) (hne : G ≠ K) : Nat.card {e : Sym2 V // e ∈ G.edgeSet} < Nat.card {e : Sym2 V // e ∈ K.edgeSet} := by sorry
