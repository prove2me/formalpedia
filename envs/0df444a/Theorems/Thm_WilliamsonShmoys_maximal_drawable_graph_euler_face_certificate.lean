-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_face_certificate
-- name    : WilliamsonShmoys.maximal_drawable_graph_euler_face_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:35:03.743031+00:00
-- url     : https://prove2.me/theorems/d16ecd9e-f113-4126-9c1f-74e1c3cba310
-- title:
--   Euler and face-incidence certificate for maximal drawable graphs
-- statement:
--   A drawable finite graph on at least three vertices that is maximal under drawable supergraph extension has a natural-number face count satisfying Euler’s equation and the face-edge incidence bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V,
      K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
