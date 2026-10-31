-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:27.007248+00:00
-- url     : https://prove2.me/theorems/707a5485-2508-4075-a69a-7b5961a94d92
-- title:
--   Subgraphs inherit a planar drawing
-- statement:
--   Every subgraph of a graph with a planar drawing on the given ordered finite vertex type has a planar drawing on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_2c2fa59c_c2a7_475f_bc59_370cb8d75cfd_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
