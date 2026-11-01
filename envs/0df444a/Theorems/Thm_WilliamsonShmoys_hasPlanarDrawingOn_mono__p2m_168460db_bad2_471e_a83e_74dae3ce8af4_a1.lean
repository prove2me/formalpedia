-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_mono__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a1
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:04.024035+00:00
-- url     : https://prove2.me/theorems/e057befb-15d5-48ea-b0e0-b77c2cbd9cb5
-- title:
--   Planar drawing is preserved under edge removal
-- statement:
--   If one graph is a subgraph of another graph with a planar drawing, the subgraph has a planar drawing using the same vertex positions and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_mono__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H) :
    HasPlanarDrawingOn H → HasPlanarDrawingOn G := by sorry
