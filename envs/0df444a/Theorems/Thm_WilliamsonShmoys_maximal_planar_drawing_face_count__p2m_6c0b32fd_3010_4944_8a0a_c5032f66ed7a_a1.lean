-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count__p2m_6c0b32fd_3010_4944_8a0a_c5032f66ed7a_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_6c0b32fd_3010_4944_8a0a_c5032f66ed7a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:32:14.870366+00:00
-- url     : https://prove2.me/theorems/2a7650ab-0d49-4561-8c94-05941238bb9e
-- title:
--   Maximal planar drawing has Euler and face-incidence counts
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type, there is a natural-number face count f satisfying Euler’s relation and the incidence inequality needed for the edge lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_6c0b32fd_3010_4944_8a0a_c5032f66ed7a_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) : ∃ f : Nat, Fintype.card V + f = M.edgeSet.ncard + 2 ∧ 2 * M.edgeSet.ncard ≤ 3 * f := by sorry
