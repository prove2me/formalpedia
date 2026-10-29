-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count_for_target_957bde25
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_for_target_957bde25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:15:32.231161+00:00
-- url     : https://prove2.me/theorems/6d51d945-c10a-4c2d-97f9-998b32849584
-- title:
--   Maximal drawable graphs have the Euler edge count
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. This removes the planar topology and Euler-counting work from the parent. A proof route is to derive connectedness and triangular faces from maximality, apply Euler’s formula to the resulting plane embedding, and count each edge twice across face boundaries. The size hypothesis is essential at the boundary: the conclusion does not assert this count for graphs on fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count_for_target_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
