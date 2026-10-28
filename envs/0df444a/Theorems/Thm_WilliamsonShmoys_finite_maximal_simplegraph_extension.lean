-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_simplegraph_extension
-- name    : WilliamsonShmoys.finite_maximal_simplegraph_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:14:29.025445+00:00
-- url     : https://prove2.me/theorems/16d0740c-f347-4cd2-91c2-229559ec5c8b
-- title:
--   Finite maximal extension for a predicate on simple graphs
-- statement:
--   For a simple graph on a finite linearly ordered vertex type, every predicate satisfied by a starting graph has a maximal satisfying extension under graph inclusion. The intended proof bounds edge cardinalities by the finite set of possible unordered pairs and maximizes among satisfying extensions. This removes the maximal-extension argument from the parent; the parent then only instantiates the predicate with planar drawability. The child’s remaining core obligation is formalizing that finite maximum and showing strict graph inclusion strictly increases edge cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_simplegraph_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by
  sorry
