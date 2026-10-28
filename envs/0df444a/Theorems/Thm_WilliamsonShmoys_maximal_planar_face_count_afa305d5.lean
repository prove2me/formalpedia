-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_afa305d5
-- name    : WilliamsonShmoys.maximal_planar_face_count_afa305d5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:16:23.774994+00:00
-- url     : https://prove2.me/theorems/9292ca2b-828b-4b83-ad8a-76361d1d48a1
-- title:
--   Euler and incidence counts for a maximal drawable graph
-- statement:
--   For a finite graph with at least three vertices, a crossing-free drawing, and maximality among drawable supergraphs on the same vertex set, there is a face count satisfying Euler’s relation and the triangular face-incidence equation. The child’s remaining core is to formalize the embedding and show maximality forces triangular faces; each edge is incident to two face sides and each triangular face contributes three incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_afa305d5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall J : SimpleGraph V, H <= J ->
      WilliamsonShmoys.HasPlanarDrawingOn J -> J = H) :
    exists f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 /\
      2 * H.edgeSet.ncard = 3 * f := by sorry
