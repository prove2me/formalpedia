-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connect_components__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
-- name    : WilliamsonShmoys.planarDrawing_connect_components__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:23.302689+00:00
-- url     : https://prove2.me/theorems/979812ef-14c0-48fc-9225-4ed9c1dbb1a6
-- title:
--   Connect components of a finite planar drawing
-- statement:
--   Any finite graph with a crossing-free drawing can be extended on the same vertex set to a connected graph with a crossing-free drawing, while preserving all original edges and therefore not decreasing the edge count. The extension is formed by joining distinct embedded components through the plane regions between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connect_components__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel H.Adj := dH
         G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
