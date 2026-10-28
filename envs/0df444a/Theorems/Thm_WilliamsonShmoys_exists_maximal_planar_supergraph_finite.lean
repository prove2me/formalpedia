-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:22:33.087882+00:00
-- url     : https://prove2.me/theorems/eea9d7cc-03c1-44ec-bfa9-de2bb13b9b15
-- title:
--   Finite maximal planar supergraph
-- statement:
--   Every graph with a planar drawing on a finite linearly ordered vertex type has an inclusion-maximal planar supergraph on the same vertices, with at least as many edges as the original.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finite
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
