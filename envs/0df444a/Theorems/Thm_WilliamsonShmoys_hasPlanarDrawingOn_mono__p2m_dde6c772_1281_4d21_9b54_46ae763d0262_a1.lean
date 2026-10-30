-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:54.450831+00:00
-- url     : https://prove2.me/theorems/4217ca6e-76db-46a5-a508-ffe6099a0b40
-- title:
--   Planar drawing passes to subgraphs
-- statement:
--   Every subgraph of a graph with a planar drawing on the same ordered vertex type has such a drawing, by reusing the vertex map and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_dde6c772_1281_4d21_9b54_46ae763d0262_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : LE.le G H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
