-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_cbce8d52_767a_43cf_a345_07ed3485307d
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cbce8d52_767a_43cf_a345_07ed3485307d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:23:20.539693+00:00
-- url     : https://prove2.me/theorems/2ca19843-80b6-412b-885e-e3f5a3e741b0
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Any graph with the supplied planar drawing has a drawable supergraph on the same finite vertex type that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cbce8d52_767a_43cf_a345_07ed3485307d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V,
        H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H := by
  sorry
