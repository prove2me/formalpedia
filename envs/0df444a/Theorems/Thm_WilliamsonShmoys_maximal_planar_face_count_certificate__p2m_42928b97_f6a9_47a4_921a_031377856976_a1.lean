-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
-- name    : WilliamsonShmoys.maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:26.183208+00:00
-- url     : https://prove2.me/theorems/6a345071-3a17-4f5f-baeb-1c2d7606cf05
-- title:
--   Face-count certificate for maximal planar drawings
-- statement:
--   A maximal drawable simple graph on at least three finite vertices has a face count satisfying Euler’s formula and the triangular face-side count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_certificate__p2m_42928b97_f6a9_47a4_921a_031377856976_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  sorry
