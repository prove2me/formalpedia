-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
-- name    : WilliamsonShmoys.maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:57.56214+00:00
-- url     : https://prove2.me/theorems/91ffed91-b87b-43c6-ba27-69e25b4e372c
-- title:
--   Euler and triangular incidence for one face count
-- statement:
--   For the connected maximal planar graph, there is one natural number of faces satisfying both Euler's equation and the triangular face-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_common_face_count__p2m_b2f31750_6395_4f01_b4dd_f5215a908d6d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    ∃ f : ℕ,
      Fintype.card V + f = N.edgeFinset.card + 2 ∧
      3 * f = 2 * N.edgeFinset.card := by sorry
