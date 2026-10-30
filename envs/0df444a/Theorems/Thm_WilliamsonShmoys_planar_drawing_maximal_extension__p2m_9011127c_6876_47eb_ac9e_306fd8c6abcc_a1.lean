-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:39:14.045974+00:00
-- url     : https://prove2.me/theorems/c8415716-12a3-43d0-afb2-534c9f55432f
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal among drawable graphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_9011127c_6876_47eb_ac9e_306fd8c6abcc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      ∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        N.edgeSet ⊆ P.edgeSet → P.edgeSet ⊆ N.edgeSet := by sorry
