-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- name    : WilliamsonShmoys.planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:49:18.606515+00:00
-- url     : https://prove2.me/theorems/3890fa6a-8c97-426e-8e8b-1860bf59eade
-- title:
--   Euler and face-incidence count for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces f satisfying Euler’s equation n + f = m + 2 and the face-boundary incidence inequality 3f ≤ 2m. The drawing’s faces and boundary walks must be formalized to prove this result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count__p2m_6bdbdb3d_755f_4cae_8333_ac9716c72254_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V)
    (hconn : K.Connected) :
    (letI : DecidableRel K.Adj := Classical.decRel _;
      exists f : Nat,
        Fintype.card V + f = K.edgeFinset.card + 2 /\
        3 * f <= 2 * K.edgeFinset.card) := by sorry
