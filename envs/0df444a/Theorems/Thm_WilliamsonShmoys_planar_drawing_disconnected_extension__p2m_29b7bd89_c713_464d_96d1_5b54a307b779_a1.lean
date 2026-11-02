-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1
-- name    : WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T08:23:53.515573+00:00
-- url     : https://prove2.me/theorems/3bd14aec-b95d-4605-ab72-e43eb10bcb26
-- title:
--   Add an edge between suitable components of a disconnected planar drawing
-- statement:
--   For a finite graph with the given crossing-free drawing, if it is disconnected, there are unreachable vertices whose connecting edge can be added while retaining a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_extension__p2m_29b7bd89_c713_464d_96d1_5b54a307b779_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) : ¬ H.Connected → ∃ u v, ¬ H.Reachable u v ∧ HasPlanarDrawingOn (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 V))) := by sorry
