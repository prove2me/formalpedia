-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_drawing_mono__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_drawing_mono__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:27.982985+00:00
-- url     : https://prove2.me/theorems/ba28770d-1829-4e55-ad98-6de96e04e619
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   If a graph is a subgraph of a graph with a crossing-free drawing on the same vertex type, then it has such a drawing as well, using the same points and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_drawing_mono__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1 {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (hGK : G ≤ K) (hK : HasPlanarDrawingOn K) : HasPlanarDrawingOn G := by sorry
