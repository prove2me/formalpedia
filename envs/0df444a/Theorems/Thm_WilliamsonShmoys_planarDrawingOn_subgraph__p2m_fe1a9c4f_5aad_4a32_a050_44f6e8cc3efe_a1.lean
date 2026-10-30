-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:13:43.167888+00:00
-- url     : https://prove2.me/theorems/bbde105b-93e1-4856-8043-6097c403f9d0
-- title:
--   Planarity is preserved by taking subgraphs
-- statement:
--   A crossing-free drawing of a graph is also a crossing-free drawing of any graph on the same vertices whose edges are a subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_fe1a9c4f_5aad_4a32_a050_44f6e8cc3efe_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by sorry
