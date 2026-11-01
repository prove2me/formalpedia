-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_face_lower__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
-- name    : WilliamsonShmoys.planar_maximal_face_lower__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:29.617806+00:00
-- url     : https://prove2.me/theorems/93495c6b-060a-4795-942d-53f57b28e4d9
-- title:
--   Maximal planar drawings have triangular faces
-- statement:
--   For a maximal planar simple graph on at least three vertices, any natural number satisfying Euler’s face-count equation gives at most three edge incidences per face on average; equivalently, twice the edge count is at most three times that face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_face_lower__p2m_2930c541_cd90_4895_988f_c75e47ffb674_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet = H.edgeSet)
    (hcard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (heuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    2 * H.edgeSet.ncard ≤ 3 * f := by sorry
