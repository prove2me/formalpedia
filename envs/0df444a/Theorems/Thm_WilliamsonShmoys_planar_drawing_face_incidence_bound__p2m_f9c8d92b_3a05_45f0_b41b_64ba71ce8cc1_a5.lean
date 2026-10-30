-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_bound__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
-- name    : WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:24.07693+00:00
-- url     : https://prove2.me/theorems/3948e52b-b0d7-479f-b947-2a84e2ebda9e
-- title:
--   Face incidence bound for a connected planar drawing
-- statement:
--   For this connected graph and drawing, every natural number satisfying the stated Euler equation obeys the target incidence inequality. This removes the incidence step from the parent. A proof route establishes the simple planar edge bound `|E| ≤ 3|V| − 6` from the drawing and combines it with the Euler equation by natural-number arithmetic. Equivalently, one can count facial boundary-walk edge occurrences, counting both sides of bridges and proving every facial boundary has length at least three. The planar bound or boundary-count argument remains to be formalized.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f ≤ 2 * H.edgeSet.ncard := by sorry
