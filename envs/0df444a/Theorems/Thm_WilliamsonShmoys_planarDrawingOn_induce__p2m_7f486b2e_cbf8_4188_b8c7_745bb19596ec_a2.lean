-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- name    : WilliamsonShmoys.planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:36:25.503901+00:00
-- url     : https://prove2.me/theorems/a22959f8-d691-4a11-85db-c547be792a19
-- title:
--   Planar drawing restricts to an induced subgraph
-- statement:
--   Restricting a crossing-free drawing to the vertices in a finite subset yields a crossing-free drawing of the induced subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_induce__p2m_7f486b2e_cbf8_4188_b8c7_745bb19596ec_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (s : Finset V) :
    HasPlanarDrawingOn (L.induce (↑s : Set V)) := by sorry
