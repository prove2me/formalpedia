-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:59:07.340898+00:00
-- url     : https://prove2.me/theorems/bda15b83-3860-44d3-89cb-6aa8bd70318c
-- title:
--   Maximal drawable extension on a finite vertex type
-- statement:
--   For any drawable graph on a finite linearly ordered vertex type, there is a drawable supergraph on the same type with at least as many edges that is maximal among drawable supergraphs. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
