-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- name    : WilliamsonShmoys.planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:58.932802+00:00
-- url     : https://prove2.me/theorems/b08e4300-e895-4d04-8414-8844a4d73c72
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   Any subgraph of a graph with a crossing-free drawing on the same vertices has such a drawing, using the original vertex placement and the arcs for its retained edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_subgraph__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  sorry
