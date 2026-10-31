-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:58.01097+00:00
-- url     : https://prove2.me/theorems/5fdd342d-dc75-47e0-8287-8202cedefb2b
-- title:
--   Planar extension with maximal planar edge count
-- statement:
--   Any drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_8dfa4b72_07b4_4156_b232_5425c6bb73fa_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
