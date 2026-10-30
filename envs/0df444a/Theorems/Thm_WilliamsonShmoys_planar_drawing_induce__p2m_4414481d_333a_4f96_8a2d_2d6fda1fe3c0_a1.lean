-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:46:02.373471+00:00
-- url     : https://prove2.me/theorems/6f8b33c2-1fca-49a3-84cc-85dc3184e01d
-- title:
--   Planar drawing restricts to induced subgraphs
-- statement:
--   Restricting a crossing-free drawing to the vertices of a finite subset gives a crossing-free drawing of the induced subgraph on that subset. The proof restricts the vertex placement and the edge arcs; it also handles the empty subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (S : Finset V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) : WilliamsonShmoys.HasPlanarDrawingOn (L.induce (↑S : Set V)) := by sorry
