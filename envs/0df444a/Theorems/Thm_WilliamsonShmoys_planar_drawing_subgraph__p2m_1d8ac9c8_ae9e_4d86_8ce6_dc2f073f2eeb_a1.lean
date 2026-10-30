-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:22:14.05906+00:00
-- url     : https://prove2.me/theorems/3aaeaa60-76be-44db-9a0c-2af1177581c5
-- title:
--   Planar drawing restricts to subgraphs
-- statement:
--   If a graph on the given finite ordered vertex type is a subgraph of a graph with a planar drawing, it also has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : HasPlanarDrawingOn H) :
    HasPlanarDrawingOn G := by
  sorry
