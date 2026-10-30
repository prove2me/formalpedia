-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:06.895513+00:00
-- url     : https://prove2.me/theorems/589dfbf2-6752-446d-86dd-1ad54b42e363
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Every graph with a drawing has an edge-inclusion-maximal planar supergraph on the same finite vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_00e8ebb5_9f6a_4f3b_a13c_8345d9aaf556_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M) :
    ∃ H : SimpleGraph V, M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet →
        HasPlanarDrawingOn K → H.edgeSet = K.edgeSet := by
  sorry
