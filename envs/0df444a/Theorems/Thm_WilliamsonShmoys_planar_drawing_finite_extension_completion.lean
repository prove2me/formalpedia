-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_extension_completion
-- name    : WilliamsonShmoys.planar_drawing_finite_extension_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:12:09.081985+00:00
-- url     : https://prove2.me/theorems/e0fffa1a-77bd-46a3-8638-4ca8efeeb7da
-- title:
--   Complete a finite sequence of planar component joins
-- statement:
--   If every disconnected planar extension of a finite graph admits a further planar extension that adds at least one edge and adds edges only between old components, then the original graph has a connected planar extension. Iterating the step terminates because each step merges components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_extension_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hstep : ∀ K : SimpleGraph V,
      L.edgeSet ⊆ K.edgeSet →
      HasPlanarDrawingOn K →
      ¬ K.Connected →
      ∃ H : SimpleGraph V,
        K.edgeSet ⊆ H.edgeSet ∧
        HasPlanarDrawingOn H ∧
        (∀ u v, H.Adj u v → K.Adj u v ∨ ¬ K.Reachable u v) ∧
        (∃ u v, H.Adj u v ∧ ¬ K.Reachable u v)) :
    ∃ H : SimpleGraph V,
      L.edgeSet ⊆ H.edgeSet ∧
      H.Connected ∧
      HasPlanarDrawingOn H := by sorry
