-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:01.86513+00:00
-- url     : https://prove2.me/theorems/ce840477-f2d7-4fa9-bef5-e1ba1a739d71
-- title:
--   A subgraph inherits a crossing-free drawing
-- statement:
--   If a graph has a crossing-free drawing and another graph on the same ordered vertex type is its subgraph, then that subgraph has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1 {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hGH : G ≤ H) : HasPlanarDrawingOn G := by sorry
