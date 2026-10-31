-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- name    : WilliamsonShmoys.planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:52:32.39024+00:00
-- url     : https://prove2.me/theorems/523c1acd-d899-4f39-911b-962863474905
-- title:
--   Augmenting a planar drawing below the triangulation bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than three times its vertex count minus six edges, it has a proper drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_strict_extension_below_bound_ce5c260b_bd9c_4523_ad2e_2ffb5e12904c
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 <= Fintype.card V)
    (hSmall : N.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ P : SimpleGraph V, N <= P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by sorry
