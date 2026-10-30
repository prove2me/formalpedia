-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:42:48.732991+00:00
-- url     : https://prove2.me/theorems/2f2c1d77-ece2-4093-80b2-27e6c334465e
-- title:
--   Euler and triangular-face equations for maximal planar drawings
-- statement:
--   For a finite drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a face count satisfying Euler's equation and the triangular face-edge incidence equation. Together these equations imply the target edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
