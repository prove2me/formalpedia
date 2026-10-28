-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_of_drawing
-- name    : WilliamsonShmoys.planar_edge_count_le_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:06:18.658997+00:00
-- url     : https://prove2.me/theorems/374007c9-6407-4902-83c7-575dff2470f5
-- title:
--   Euler upper bound for a planar simple graph
-- statement:
--   A simply drawn planar graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_le_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
