-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5
-- name    : WilliamsonShmoys.planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T03:33:13.81899+00:00
-- url     : https://prove2.me/theorems/b83e28ac-6e67-475e-a82b-ea2b7daee602
-- title:
--   Simple planar graphs satisfy the edge bound
-- statement:
--   A crossing-free drawing of a finite simple graph with at least three vertices implies the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarSimpleEdgeBound__p2m_4a6667dc_3f5b_4370_a682_d1aef720dceb_a5 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
