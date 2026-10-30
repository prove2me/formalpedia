-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound
-- name    : WilliamsonShmoys.planar_edge_card_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:42:17.178547+00:00
-- url     : https://prove2.me/theorems/f9ab9c4f-5b60-402d-9c7d-53ffa1677423
-- title:
--   Planar simple graphs have at most 3n minus 6 edges
-- statement:
--   A finite simple graph with at least three vertices and a planar drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_card_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
