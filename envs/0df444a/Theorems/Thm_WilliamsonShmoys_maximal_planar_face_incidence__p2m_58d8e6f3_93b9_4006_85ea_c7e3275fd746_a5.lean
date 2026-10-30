-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- name    : WilliamsonShmoys.maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:00:15.44999+00:00
-- url     : https://prove2.me/theorems/7d7aec35-2e39-4f0c-96ea-78f8bd4c0509
-- title:
--   Triangular-face edge incidence count
-- statement:
--   For an inclusion-maximal drawable graph on at least three vertices and a face count satisfying Euler’s equation, maximality forces triangular face boundaries; double-counting face-edge incidences gives three times the face count equal to twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_incidence__p2m_58d8e6f3_93b9_4006_85ea_c7e3275fd746_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = L.edgeSet.ncard + 2) :
    3 * f = 2 * L.edgeSet.ncard := by sorry
