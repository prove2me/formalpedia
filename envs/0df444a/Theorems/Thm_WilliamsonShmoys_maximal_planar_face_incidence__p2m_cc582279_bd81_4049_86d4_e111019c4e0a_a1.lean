-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_incidence__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
-- name    : WilliamsonShmoys.maximal_planar_face_incidence__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T12:41:55.172855+00:00
-- url     : https://prove2.me/theorems/742d4241-824b-4005-9871-4632233b6a91
-- title:
--   Triangular face incidence equation for the Euler count
-- statement:
--   For the same maximal drawable graph, any natural face count satisfying Euler’s equation also satisfies the triangular face-edge incidence equation. The independent proof route is to show maximality forces every face to be triangular and then count incidences, with each edge contributing two sides. The drawing definition has no explicit face structure, so constructing and reasoning about that structure is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_incidence__p2m_cc582279_bd81_4049_86d4_e111019c4e0a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    3 * f = 2 * K.edgeSet.ncard := by sorry
