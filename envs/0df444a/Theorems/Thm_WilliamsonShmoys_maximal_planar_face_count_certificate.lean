-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_certificate
-- name    : WilliamsonShmoys.maximal_planar_face_count_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:18:52.785447+00:00
-- url     : https://prove2.me/theorems/1e96ab19-a872-4ea9-a2b0-fe57939c8895
-- title:
--   Face-count certificate for a maximal planar graph
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, there is a natural number of faces satisfying both Euler’s formula and the triangular-face edge-incidence count. The boundary condition of at least three vertices is needed for maximal planar graphs to have triangular faces; maximality is used to rule out disconnected components and nontriangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_face_count_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
