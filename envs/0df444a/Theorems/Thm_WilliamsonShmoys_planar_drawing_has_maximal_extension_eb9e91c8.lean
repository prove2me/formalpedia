-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_eb9e91c8
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_eb9e91c8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:17:52.796895+00:00
-- url     : https://prove2.me/theorems/4443922d-1b83-4940-9837-5c8ec5e003c2
-- title:
--   Extend a drawable graph to a maximal drawable graph
-- statement:
--   Extend the given drawable graph, on the same finite vertex type, to one maximal under graph inclusion among graphs with such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_eb9e91c8
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
