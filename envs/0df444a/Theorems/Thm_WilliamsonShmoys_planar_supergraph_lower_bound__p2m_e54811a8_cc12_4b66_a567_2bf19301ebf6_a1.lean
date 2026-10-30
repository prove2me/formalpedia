-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
-- name    : WilliamsonShmoys.planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:12:49.279874+00:00
-- url     : https://prove2.me/theorems/219a8e3b-c7d8-43b3-9ee1-a4b3ebf8e3f2
-- title:
--   Planar completion reaches the extremal edge count
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is at least 3|V|−6. Extend by adding drawable edges to a maximal planar supergraph, then use triangulation and Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_lower_bound__p2m_e54811a8_cc12_4b66_a567_2bf19301ebf6_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
