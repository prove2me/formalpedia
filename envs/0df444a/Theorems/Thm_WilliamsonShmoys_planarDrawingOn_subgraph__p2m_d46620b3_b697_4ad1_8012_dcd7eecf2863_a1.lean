-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a1
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:26:28.907484+00:00
-- url     : https://prove2.me/theorems/62fe291d-2782-4595-b4f7-2d0697d26e0b
-- title:
--   A subgraph inherits a crossing-free drawing
-- statement:
--   Restricting the edge relation of a graph with a crossing-free drawing preserves the drawing property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
