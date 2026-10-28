-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_96423339_d6c7_499e_a706_076681b42078
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_96423339_d6c7_499e_a706_076681b42078
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:28:14.116164+00:00
-- url     : https://prove2.me/theorems/98db47a5-076d-4eaa-9fbf-8ca44fee6b61
-- title:
--   Finite maximal drawable extension
-- statement:
--   For a finite ordered vertex type, every graph with a planar drawing has a drawable supergraph that is maximal among drawable graphs on the same vertex set. The size hypothesis is retained to match the parent, although finite maximization itself does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_96423339_d6c7_499e_a706_076681b42078
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        ∀ (M : SimpleGraph V), L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
