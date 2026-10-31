-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:34:39.218666+00:00
-- url     : https://prove2.me/theorems/3f0401d4-e7c7-4ba4-b68f-33f604120dbf
-- title:
--   Planar drawings restrict to subgraphs
-- statement:
--   A crossing-free drawing on a fixed vertex type restricts to any graph whose edges are a subset of the drawn graph’s edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_8fae69ca_ae24_46cb_a1af_2dc3b1fd2851_a2 {V : Type} [Fintype V] [LinearOrder V] {A B : SimpleGraph V} (hAB : A ≤ B) (hB : HasPlanarDrawingOn B) : HasPlanarDrawingOn A := by sorry
