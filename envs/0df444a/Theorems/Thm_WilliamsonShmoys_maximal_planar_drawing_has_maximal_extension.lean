-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_maximal_extension
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:37:51.926953+00:00
-- url     : https://prove2.me/theorems/93e57e72-aa98-4886-97c3-7cce49ee49ce
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) := by sorry
