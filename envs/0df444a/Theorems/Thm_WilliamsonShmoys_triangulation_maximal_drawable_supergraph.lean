-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_maximal_drawable_supergraph
-- name    : WilliamsonShmoys.triangulation_maximal_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:01:16.303078+00:00
-- url     : https://prove2.me/theorems/8ef29375-393d-43ec-a424-f60475f2b306
-- title:
--   Choose a maximal drawable supergraph for triangulation completion
-- statement:
--   Every drawable graph on this finite vertex type is contained in a drawable supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_maximal_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by sorry
