-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:44.826983+00:00
-- url     : https://prove2.me/theorems/e54811a8-cc12-4b66-a567-2bf19301ebf6
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
