-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_face_count
-- name    : WilliamsonShmoys.maximal_planar_triangular_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:10:15.440982+00:00
-- url     : https://prove2.me/theorems/2a71df23-e175-4bb9-8167-b8de055bb1a0
-- title:
--   Triangular face-edge incidence count
-- statement:
--   For a maximal drawable graph on at least three vertices, any face count satisfying Euler’s equation obeys the triangular-face incidence equation. The proof route is to show maximality forces each face boundary to have length three, then double-count incidences between faces and edges. This is the step that uses maximality and supplies the second equation once the Euler face count is known.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangular_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f = 2 * L.edgeSet.ncard := by sorry
