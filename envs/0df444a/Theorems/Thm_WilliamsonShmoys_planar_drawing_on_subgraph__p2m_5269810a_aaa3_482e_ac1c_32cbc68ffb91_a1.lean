-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- name    : WilliamsonShmoys.planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:21.74869+00:00
-- url     : https://prove2.me/theorems/17276304-0d54-434e-83f4-2a52a037e201
-- title:
--   The drawing property passes to subgraphs
-- statement:
--   If a graph has a drawing satisfying the specified vertex-placement and edge-arc conditions, every subgraph on the same vertex type has such a drawing by reusing the same placement and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_subgraph__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : HasPlanarDrawingOn G) :
    HasPlanarDrawingOn H := by sorry
