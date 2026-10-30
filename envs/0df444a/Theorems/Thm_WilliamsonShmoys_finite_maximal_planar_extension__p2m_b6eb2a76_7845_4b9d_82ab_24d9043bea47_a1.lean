-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:39.152582+00:00
-- url     : https://prove2.me/theorems/07b78964-cbaf-4bb7-98dc-a4ce7ae0f70a
-- title:
--   Finite maximal planar extension
-- statement:
--   Every planar graph on a finite vertex type with at least three vertices has an inclusion-maximal planar supergraph on that same vertex type; the original graph’s edge count is no larger than the extension’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_planar_extension__p2m_b6eb2a76_7845_4b9d_82ab_24d9043bea47_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) := by sorry
