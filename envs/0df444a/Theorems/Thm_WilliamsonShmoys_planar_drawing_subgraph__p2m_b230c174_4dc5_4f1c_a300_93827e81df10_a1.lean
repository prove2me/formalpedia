-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:41:45.02207+00:00
-- url     : https://prove2.me/theorems/3729d222-585b-41b2-81a8-cfdc38e365f2
-- title:
--   A subgraph of a drawable graph is drawable
-- statement:
--   If a graph is a subgraph of a graph with a crossing-free drawing, then it has a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_b230c174_4dc5_4f1c_a300_93827e81df10_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by sorry
