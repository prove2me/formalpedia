-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:24:52.506583+00:00
-- url     : https://prove2.me/theorems/2c017386-df97-4105-beb8-4314705609bf
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Every planar graph on a finite ordered vertex type has an inclusion-maximal planar supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_completion_55e40668_6c6c_445f_853d_a7074df51c4e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
