-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:46:18.916885+00:00
-- url     : https://prove2.me/theorems/9382165c-9a01-4b7f-aba6-3920ad4981e4
-- title:
--   Euler edge bound for a finite planar drawing
-- statement:
--   Every drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
