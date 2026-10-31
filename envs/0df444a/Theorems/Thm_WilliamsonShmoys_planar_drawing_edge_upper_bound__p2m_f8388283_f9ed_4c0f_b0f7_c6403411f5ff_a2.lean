-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:03.575276+00:00
-- url     : https://prove2.me/theorems/49092f42-4606-480d-84ab-7522b76f4e32
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Any graph with the bundled crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This removes the general planar edge bound from the parent. A proof route is Euler’s formula and face-degree counting, with disconnected components handled as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_f8388283_f9ed_4c0f_b0f7_c6403411f5ff_a2 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
