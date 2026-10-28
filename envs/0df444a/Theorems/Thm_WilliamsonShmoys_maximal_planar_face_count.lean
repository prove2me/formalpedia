-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count
-- name    : WilliamsonShmoys.maximal_planar_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:17:43.29653+00:00
-- url     : https://prove2.me/theorems/bb723121-21f5-4e26-8f7d-2608805e93b4
-- title:
--   Euler and incidence counts for maximal planar drawings
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a natural number of faces satisfying Euler's equation and the triangular face-edge incidence equation. These two counts imply the target edge formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
