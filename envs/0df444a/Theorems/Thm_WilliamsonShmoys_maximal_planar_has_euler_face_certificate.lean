-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_has_euler_face_certificate
-- name    : WilliamsonShmoys.maximal_planar_has_euler_face_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:21:12.515684+00:00
-- url     : https://prove2.me/theorems/836eb74d-cbb0-429f-846d-f0bcd224a188
-- title:
--   Maximal planar drawing yields an Euler face-count certificate
-- statement:
--   An inclusion-maximal simple graph with at least three vertices and the supplied crossing-free drawing has a natural face count satisfying Euler’s equation and the triangular face-incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_has_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    ∃ f : ℕ, K.edgeSet.ncard + 2 = Fintype.card V + f ∧
      2 * K.edgeSet.ncard ≤ 3 * f := by sorry
