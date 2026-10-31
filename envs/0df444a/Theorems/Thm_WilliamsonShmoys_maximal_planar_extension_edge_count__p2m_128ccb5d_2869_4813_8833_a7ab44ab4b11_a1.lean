-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:21.705027+00:00
-- url     : https://prove2.me/theorems/8d45bf42-38ea-432e-b84b-d41270aef8ba
-- title:
--   Triangulated planar extension edge count
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertex set whose edge count is 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_128ccb5d_2869_4813_8833_a7ab44ab4b11_a1 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, W ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
