-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:26:34.20104+00:00
-- url     : https://prove2.me/theorems/adc3d82d-749f-4979-9493-3fcc8941be47
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite fixed vertex set is contained in a drawable supergraph that is inclusion-maximal among drawable supergraphs on that set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      ∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        N.edgeSet ⊆ P.edgeSet →
        P.edgeSet ⊆ N.edgeSet := by sorry
