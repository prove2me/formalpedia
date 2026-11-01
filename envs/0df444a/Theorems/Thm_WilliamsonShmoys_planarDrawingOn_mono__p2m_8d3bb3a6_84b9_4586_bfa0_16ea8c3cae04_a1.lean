-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- name    : WilliamsonShmoys.planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:33:51.775458+00:00
-- url     : https://prove2.me/theorems/ba4b21d9-6eff-45fe-8239-9fec8addcf54
-- title:
--   Planar drawing is preserved under edge restriction
-- statement:
--   If one graph is a subgraph of another graph with a crossing-free drawing, then the smaller graph has a crossing-free drawing on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_mono__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
