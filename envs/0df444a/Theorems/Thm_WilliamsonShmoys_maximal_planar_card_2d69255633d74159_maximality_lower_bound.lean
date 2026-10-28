-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_card_2d69255633d74159_maximality_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_card_2d69255633d74159_maximality_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:55:33.223359+00:00
-- url     : https://prove2.me/theorems/dde9da7a-0c7c-4a64-945e-a71885d6cff1
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal simply drawn planar graph on at least three vertices has at least 3|V| − 6 edges. This removes the maximality-based lower-bound obligation from the parent. A proof route is to show that maximality forces connectedness and triangular faces, then combine planar Euler’s formula with the fact that every edge borders two face sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_card_2d69255633d74159_maximality_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P.edgeSet ⊆ Q.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q.edgeSet ⊆ P.edgeSet) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
