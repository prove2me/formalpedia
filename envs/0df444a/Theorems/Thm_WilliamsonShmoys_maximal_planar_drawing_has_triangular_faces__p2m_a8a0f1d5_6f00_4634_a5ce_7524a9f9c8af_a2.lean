-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:21:04.633925+00:00
-- url     : https://prove2.me/theorems/68b7ee61-4139-4050-b42c-be1c462d54e2
-- title:
--   Maximal planar drawings have triangular face boundaries
-- statement:
--   Construct a finite indexed collection of triangular face boundaries from the drawing, using only edges of L, with every edge incident to exactly two indexed faces. When there are exactly three vertices, the two face indices may have the same boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
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
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) := by sorry
