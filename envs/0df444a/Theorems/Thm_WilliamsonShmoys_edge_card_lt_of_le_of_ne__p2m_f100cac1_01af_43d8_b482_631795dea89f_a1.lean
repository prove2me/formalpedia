-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_lt_of_le_of_ne__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- name    : WilliamsonShmoys.edge_card_lt_of_le_of_ne__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:18.21699+00:00
-- url     : https://prove2.me/theorems/02a7bc58-dc6a-4722-90e1-33c6e9515334
-- title:
--   Proper graph extensions increase finite edge count
-- statement:
--   For finite V, a proper simple-graph extension has strictly more edges. This removes the parent’s edge-count comparison. A proof route is to translate graph inclusion into inclusion of finite edge subtypes, show the inclusion is proper from G ≠ H, and apply strict cardinality growth for finite sets. The hypotheses retain both the finite vertex type needed for finite edge sets and the graph inclusion needed for monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_card_lt_of_le_of_ne__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1 {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hGH : G ≤ H) (hne : G ≠ H) : Nat.card {e : Sym2 V // e ∈ G.edgeSet} < Nat.card {e : Sym2 V // e ∈ H.edgeSet} := by sorry
