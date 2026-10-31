-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_max_edge_card__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:21.52977+00:00
-- url     : https://prove2.me/theorems/69ec58a5-aab3-4dc7-a449-f1759fd682d8
-- title:
--   A drawable supergraph with maximum edge count
-- statement:
--   Among drawable supergraphs of Q, there is one whose edge count is at least that of every other drawable supergraph. This isolates the finite maximization step from the parent. A proof route is to consider the finite powerset of the possible edges on V, restrict to edge sets representing drawable graphs extending Q, note that this family is nonempty because it contains Q, and select an element with maximal cardinality. The drawing and extension conditions are retained for every candidate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_max_edge_card__p2m_f100cac1_01af_43d8_b482_631795dea89f_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ ∀ S : SimpleGraph V, Q ≤ S → HasPlanarDrawingOn S → Nat.card {e : Sym2 V // e ∈ S.edgeSet} ≤ Nat.card {e : Sym2 V // e ∈ R.edgeSet} := by sorry
