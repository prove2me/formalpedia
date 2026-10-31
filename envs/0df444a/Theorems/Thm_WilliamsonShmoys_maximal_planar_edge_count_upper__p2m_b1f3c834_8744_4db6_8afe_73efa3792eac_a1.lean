-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:10:58.806779+00:00
-- url     : https://prove2.me/theorems/fda861fd-855b-4561-971f-8551142822a0
-- title:
--   Extremal edge bound for a finite drawable graph
-- statement:
--   Any finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the standard planar extremal bound, including disconnected drawings and the three-vertex boundary case. It supplies the target’s upper inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) (hV : 3 ≤ Fintype.card V) : P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
