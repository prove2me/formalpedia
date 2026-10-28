-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_search_maximal_planar_extension
-- name    : WilliamsonShmoys.finite_search_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:40:58.147419+00:00
-- url     : https://prove2.me/theorems/acfd29ba-366e-4c7e-9271-4f39dd2cec13
-- title:
--   A planar extension maximizing edge count exists
-- statement:
--   Among planar supergraphs of a given planar graph on a finite vertex type, one has edge count at least that of every planar supergraph containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_search_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
