-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_on_maximal_supergraph
-- name    : WilliamsonShmoys.finite_planar_drawing_on_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:13:48.015918+00:00
-- url     : https://prove2.me/theorems/c1e87dd5-f63a-42a8-a1cd-0ba5a41f5497
-- title:
--   A finite planar drawing has a maximal planar supergraph
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_planar_drawing_on_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V, HasPlanarDrawingOn U ∧
      (∀ u v, T.Adj u v → U.Adj u v) ∧
      (∀ W : SimpleGraph V, HasPlanarDrawingOn W →
        (∀ u v, U.Adj u v → W.Adj u v) → W = U) := by sorry
