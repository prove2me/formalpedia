-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_e5a7f9d6
-- name    : WilliamsonShmoys.maximal_planar_edge_count_e5a7f9d6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:26:54.470323+00:00
-- url     : https://prove2.me/theorems/282b0fbb-8bf3-4928-aeff-4b48ed6fb01f
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal planar graph on a finite linearly ordered vertex type with at least three vertices has exactly 3|V|−6 edges. The lower bound includes the three-vertex case, where maximality forces all three edges. The proof route is to show that a maximal planar drawing has triangular faces and then apply Euler’s formula; formalizing that topological argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_e5a7f9d6
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M ≤ L) :
    (L.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
