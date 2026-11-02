-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- name    : WilliamsonShmoys.planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:41:04.414812+00:00
-- url     : https://prove2.me/theorems/ba4d93bf-eea7-43c2-9f7f-9dca9d5a1521
-- title:
--   Restrict a planar drawing to a subgraph
-- statement:
--   If M is a subgraph of N and N has the specified crossing-free drawing, the same vertex placement and edge arcs give a drawing of M.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_restrict_subgraph__p2m_6d91b10d_a30f_4f1a_8acb_96a7ed12e6b9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
