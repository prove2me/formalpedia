-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
-- name    : WilliamsonShmoys.maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T19:43:11.808988+00:00
-- url     : https://prove2.me/theorems/2b92d8e9-77cc-417a-8c50-09970fb055b4
-- title:
--   Maximality forces triangular face boundaries
-- statement:
--   For a face system whose boundaries use L's edges and have size at least three, show maximality forces every boundary to have size exactly three. The proof route is to show a longer facial cycle permits adding a missing chord while preserving planarity, contradicting hMax. The boundary-size lower bound and edge-incidence condition are retained as hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (F : Type) (faceInst : Fintype F)
    (boundary : F → Finset (Sym2 V))
    (hsize : ∀ f, 3 ≤ (boundary f).card)
    (hmem : ∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet)
    (hinc : ∀ e ∈ L.edgeSet,
      ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2)
    (hCard : 3 ≤ Fintype.card V) :
    ∀ f, (boundary f).card = 3 := by sorry
