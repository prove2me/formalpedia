-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- name    : WilliamsonShmoys.maximal_planar_face_incidence__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:58.145203+00:00
-- url     : https://prove2.me/theorems/aca1b5ba-75d7-404d-be10-c2c6ea433783
-- title:
--   Maximal planar face incidence count
-- statement:
--   For a maximal drawable simple graph on at least three vertices, any face count satisfying Euler's equation also satisfies the triangular face-incidence equation. This removes the maximality-to-triangulation and incidence-counting work from the parent. A proof route is to obtain a plane embedding, prove maximality rules out nontriangular face boundaries by adding a diagonal inside such a face, and count that every edge contributes two face sides. The Euler premise identifies the supplied natural number with the embedding's face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_incidence__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M)
    (f : ℕ) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    Fintype.card V + f = M.edgeFinset.card + 2 →
      3 * f = 2 * M.edgeFinset.card := by sorry
