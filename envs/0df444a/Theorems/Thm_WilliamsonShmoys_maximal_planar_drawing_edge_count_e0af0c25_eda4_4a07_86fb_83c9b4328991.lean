-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:25:28.525918+00:00
-- url     : https://prove2.me/theorems/483a97fb-9b30-4df1-b13e-ac9cf6a4e518
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite ordered vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges. The lower bound of three vertices is needed for the maximal planar graph edge formula, including the equality boundary at three vertices. The child removes the geometric and Euler-counting work from the parent. A proof route is to show any nontriangular face permits a missing edge to be added without crossings, contradicting maximality, then apply Euler’s formula to the resulting triangulation. The triangulation and Euler argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_e0af0c25_eda4_4a07_86fb_83c9b4328991
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
