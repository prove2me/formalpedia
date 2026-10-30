-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:12.10876+00:00
-- url     : https://prove2.me/theorems/dc333b6e-8abf-48c5-ac8f-62c976c7967e
-- title:
--   Maximality forces the extremal edge count
-- statement:
--   An edge-maximal graph with the specified drawing and at least three vertices has at least 3|V|−6 edges. Maximality rules out adding any drawable edge; the intended proof establishes connectedness and triangular faces, then applies Euler’s formula and counts each edge twice among face boundaries. Together with the extremal upper bound, this yields equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_b1f3c834_8744_4db6_8afe_73efa3792eac_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (hDraw : HasPlanarDrawingOn P) (hV : 3 ≤ Fintype.card V) (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q → Q ≤ P) : 3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by sorry
