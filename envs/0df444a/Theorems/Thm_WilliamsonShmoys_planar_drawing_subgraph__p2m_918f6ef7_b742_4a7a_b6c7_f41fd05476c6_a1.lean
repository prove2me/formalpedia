-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:16.992076+00:00
-- url     : https://prove2.me/theorems/fda6a6cf-d42d-42c4-9cb0-31cf184a33e2
-- title:
--   A subgraph of a drawable graph is drawable
-- statement:
--   Removing edges from a graph with a planar drawing preserves the drawing on the same ordered vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G) (hG : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by sorry
