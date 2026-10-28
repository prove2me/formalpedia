-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_system__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
-- name    : WilliamsonShmoys.maximal_planar_face_system__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:43:03.778992+00:00
-- url     : https://prove2.me/theorems/d66b5607-c7a5-4612-90ba-2711f14e2556
-- title:
--   A maximal planar drawing has a finite face system
-- statement:
--   From the crossing-free drawing and maximality, construct a finite collection of face boundaries. Each boundary contains at least three edges, uses only edges of L, and each edge of L belongs to exactly two indexed boundaries. The route is to extract the planar embedding and its face boundaries, using maximality to rule out degenerate boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_system__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, 3 ≤ (boundary f).card) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) := by sorry
