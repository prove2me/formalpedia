-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_6daa1fb6
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_6daa1fb6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:01:15.585492+00:00
-- url     : https://prove2.me/theorems/8ff31692-88cf-45a5-a0a6-78f553175dcb
-- title:
--   A finite drawable supergraph can be chosen edge-maximal
-- statement:
--   Any drawable simple graph on a finite vertex type has a drawable supergraph on that type with no strict drawable supergraph. The result also applies to an empty vertex type and does not require a minimum vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_6daa1fb6
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, HasPlanarDrawingOn Y ∧
      (∀ u v, X.Adj u v → Y.Adj u v) ∧
      ∀ Z : SimpleGraph V, HasPlanarDrawingOn Z →
        (∀ u v, Y.Adj u v → Z.Adj u v) → Z = Y := by sorry
