-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension
-- name    : WilliamsonShmoys.maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:20:36.161778+00:00
-- url     : https://prove2.me/theorems/9ae89736-1dc3-4a25-8cd6-f72b15c31aa4
-- title:
--   Inclusion-maximal planar supergraph
-- statement:
--   Every finite simple graph with a drawing has a drawing-preserving supergraph on the same vertex type that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNdraw : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      (∀ K : SimpleGraph V, M.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → K = M) := by
  sorry
