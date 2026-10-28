-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_equations
-- name    : WilliamsonShmoys.maximal_planar_face_count_equations
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:40:10.331994+00:00
-- url     : https://prove2.me/theorems/c652b7f6-4a05-4579-9065-142e9b662252
-- title:
--   Euler and incidence equations for maximal drawable graphs
-- statement:
--   For a drawable graph on at least three vertices that is maximal under drawable edge extensions on the same vertex set, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_equations
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
