-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card
-- name    : WilliamsonShmoys.maximal_planar_edge_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:04:26.436181+00:00
-- url     : https://prove2.me/theorems/21f7ea96-a838-42a7-be86-b36b25664512
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A simple graph maximal among graphs drawable on the same finite ordered vertex type, with at least three vertices, has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_card {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hMax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J) (hCard : 3 ≤ Fintype.card V) : J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
