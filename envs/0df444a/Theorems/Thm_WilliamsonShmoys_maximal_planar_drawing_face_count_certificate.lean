-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:32:18.595965+00:00
-- url     : https://prove2.me/theorems/1855d0f3-3c0a-4e0d-ada7-91320079fa9b
-- title:
--   Euler and face-incidence certificate for maximal planar drawings
-- statement:
--   For a maximal crossing-free drawing on at least three vertices, there is a face count f satisfying Euler’s formula and the triangular-face incidence count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_face_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
