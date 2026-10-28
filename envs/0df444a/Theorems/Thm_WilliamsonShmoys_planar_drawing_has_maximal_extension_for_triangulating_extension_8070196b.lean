-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:03:45.62077+00:00
-- url     : https://prove2.me/theorems/9efd8c7b-869a-48bd-9e68-e98bcd6ac9c8
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulating_extension_8070196b
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      HasPlanarDrawingOn U ∧
      ∀ W : SimpleGraph V,
        U.edgeSet ⊆ W.edgeSet →
        HasPlanarDrawingOn W →
        W.edgeSet ⊆ U.edgeSet := by sorry
