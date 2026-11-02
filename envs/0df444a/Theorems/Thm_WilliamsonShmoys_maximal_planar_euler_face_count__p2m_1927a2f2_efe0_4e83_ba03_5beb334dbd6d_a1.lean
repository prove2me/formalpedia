-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:43:30.194953+00:00
-- url     : https://prove2.me/theorems/842d51ec-371b-408a-a7fe-9c9e23312f53
-- title:
--   Euler and face-incidence counts for maximal planar drawings
-- statement:
--   For a finite, linearly ordered vertex type with at least three vertices, a graph with the stated drawing that is maximal among drawable supergraphs has a face count satisfying Euler’s formula and the triangular-face incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_face_count__p2m_1927a2f2_efe0_4e83_ba03_5beb334dbd6d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    ∃ f : ℕ,
      f + Fintype.card V = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
