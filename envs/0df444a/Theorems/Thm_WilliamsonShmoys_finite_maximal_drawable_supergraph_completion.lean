-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph_completion
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:01:54.666063+00:00
-- url     : https://prove2.me/theorems/62324269-4813-411d-8f80-c0c852eebbc9
-- title:
--   Finite maximal drawable supergraph completion
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ K : SimpleGraph V,
      T ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
