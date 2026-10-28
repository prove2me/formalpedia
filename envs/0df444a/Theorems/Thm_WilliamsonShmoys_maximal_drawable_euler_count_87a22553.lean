-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_euler_count_87a22553
-- name    : WilliamsonShmoys.maximal_drawable_euler_count_87a22553
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:42:46.951093+00:00
-- url     : https://prove2.me/theorems/68a44d12-3e5f-406a-a171-0bd7422aa7be
-- title:
--   A maximal drawable graph has the planar Euler edge count
-- statement:
--   This is the remaining planar topology result. A proof route is to use maximality to show the drawing is connected and every face is triangular, then apply Euler’s formula and count incidences between faces and edges. The hypothesis |V| ≥ 3 is essential for the stated planar maximal-graph edge formula and includes the triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_euler_count_87a22553 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
