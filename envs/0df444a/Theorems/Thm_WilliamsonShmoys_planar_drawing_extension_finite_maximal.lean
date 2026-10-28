-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_finite_maximal
-- name    : WilliamsonShmoys.planar_drawing_extension_finite_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:44:44.302133+00:00
-- url     : https://prove2.me/theorems/29785218-614c-48d7-81cc-d617b4a18f25
-- title:
--   Extend a drawable graph to a finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a fixed finite vertex type is contained in a drawable graph with no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_extension_finite_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      N.edgeSet ⊆ P.edgeSet ∧
      ∀ Q : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn Q →
        P.edgeSet ⊆ Q.edgeSet → Q.edgeSet ⊆ P.edgeSet := by sorry
