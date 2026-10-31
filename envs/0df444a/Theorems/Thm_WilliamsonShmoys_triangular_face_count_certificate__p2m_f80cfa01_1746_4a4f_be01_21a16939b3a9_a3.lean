-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_face_count_certificate__p2m_f80cfa01_1746_4a4f_be01_21a16939b3a9_a3
-- name    : WilliamsonShmoys.triangular_face_count_certificate__p2m_f80cfa01_1746_4a4f_be01_21a16939b3a9_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:53.24276+00:00
-- url     : https://prove2.me/theorems/40de2556-ef98-4476-81bc-7fb3a0869be7
-- title:
--   Euler and triangular face-count equations for a maximal planar drawing
-- statement:
--   A finite graph on at least three vertices that is maximal among drawable supergraphs has a face count satisfying Euler’s equation and the triangular edge-side count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangular_face_count_certificate__p2m_f80cfa01_1746_4a4f_be01_21a16939b3a9_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    ∃ f : ℕ, f + Fintype.card V = N.edgeSet.ncard + 2 ∧
      3 * f = 2 * N.edgeSet.ncard := by sorry
