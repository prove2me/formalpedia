-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:23:26.578929+00:00
-- url     : https://prove2.me/theorems/25f82443-743e-4a18-b02a-1b38fccc3b9e
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph that is maximal among drawable supergraphs under inclusion. This follows by choosing a drawable supergraph with the largest edge set among the finitely many simple graphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_718d0665_f14e_4e4a_9ebf_3d91778b5251_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N := by sorry
