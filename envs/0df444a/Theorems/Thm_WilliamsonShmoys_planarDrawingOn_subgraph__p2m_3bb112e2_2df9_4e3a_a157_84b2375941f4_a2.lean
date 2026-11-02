-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:55:52.61008+00:00
-- url     : https://prove2.me/theorems/2722470a-d1b9-4fff-b251-3da7344075b7
-- title:
--   Planar drawing restricts to subgraphs
-- statement:
--   A subgraph of a graph with a planar drawing on the same ordered vertex type has a planar drawing, using the same positions and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_subgraph__p2m_3bb112e2_2df9_4e3a_a157_84b2375941f4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : HasPlanarDrawingOn G) : HasPlanarDrawingOn H := by sorry
