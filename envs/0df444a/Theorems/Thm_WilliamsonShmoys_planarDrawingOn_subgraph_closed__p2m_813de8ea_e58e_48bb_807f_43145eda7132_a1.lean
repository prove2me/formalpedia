-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- name    : WilliamsonShmoys.planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:08.750396+00:00
-- url     : https://prove2.me/theorems/68587ba6-f705-45c4-9184-9350ebf94dcc
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   Any subgraph of a graph with a crossing-free drawing on the same vertex set also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_subgraph_closed__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : HasPlanarDrawingOn H) : HasPlanarDrawingOn G := by sorry
