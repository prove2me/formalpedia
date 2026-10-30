-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_completion__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:59:40.724996+00:00
-- url     : https://prove2.me/theorems/45eaf98a-1ab5-4579-a2bf-b3b8b7295ef9
-- title:
--   Edge-maximal drawable completion
-- statement:
--   For a finite vertex type, every drawable graph has a drawable supergraph whose edge count is at least that of every other drawable supergraph of the original graph. This follows by maximizing edge count over the finite family of simple graphs on the vertex type; the original graph witnesses that the family is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_maximal_completion__p2m_0fb3eb1a_7dcf_4fa9_a911_841bd56bc763_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard ∧
      ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        N.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
