-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:43.91095+00:00
-- url     : https://prove2.me/theorems/c8d2e80c-d8a1-4ce7-8838-7e9b10da8c57
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges. The standard route shows maximality forces connectivity and triangular faces, then counts face-edge incidences and applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_d16397ab_f97b_4b48_8e65_cb91b43850d6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V, H ≤ H' → HasPlanarDrawingOn H' → H' = H) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  sorry
