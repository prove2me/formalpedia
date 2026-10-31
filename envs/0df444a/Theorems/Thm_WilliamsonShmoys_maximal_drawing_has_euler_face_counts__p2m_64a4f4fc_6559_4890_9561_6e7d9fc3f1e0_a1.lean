-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- name    : WilliamsonShmoys.maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:33.576969+00:00
-- url     : https://prove2.me/theorems/a7a27be2-fbb8-44ae-9ce4-aea6abd1f255
-- title:
--   Euler and triangular-face counts for a maximal drawable graph
-- statement:
--   For a drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type, there is a face count f satisfying Euler’s equation and the triangular face-edge incidence equation. The boundary case of three vertices is covered: maximality forces the triangle, whose sphere embedding has two triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_has_euler_face_counts__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧ 3 * f = 2 * K.edgeSet.ncard := by
  sorry
