-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_f3620a14
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension_f3620a14
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:19:38.577924+00:00
-- url     : https://prove2.me/theorems/fb362d9b-88f1-437f-b078-7952da13ef95
-- title:
--   Finite maximal planar drawing extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same vertex type that is maximal under graph inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension_f3620a14
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      T ≤ S ∧
      ∀ R : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn R → S ≤ R → R ≤ S := by sorry
