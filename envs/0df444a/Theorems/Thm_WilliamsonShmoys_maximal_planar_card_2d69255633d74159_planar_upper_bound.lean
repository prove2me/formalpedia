-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_card_2d69255633d74159_planar_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_card_2d69255633d74159_planar_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:54:34.141985+00:00
-- url     : https://prove2.me/theorems/04150578-546e-4101-95cf-54180ec28486
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every simply drawn planar graph on at least three vertices has at most 3|V| − 6 edges. This removes the upper-bound obligation from the parent. A proof route is to derive the planar Euler inequality from the drawing, treating connected components, and use that each face boundary has length at least three in a simple graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_card_2d69255633d74159_planar_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
