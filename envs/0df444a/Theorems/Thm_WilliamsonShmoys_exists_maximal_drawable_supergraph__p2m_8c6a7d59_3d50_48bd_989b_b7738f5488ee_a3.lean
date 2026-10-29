-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T21:24:30.682572+00:00
-- url     : https://prove2.me/theorems/38f545c7-bfae-46f4-84f5-59810c5adbe6
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_8c6a7d59_3d50_48bd_989b_b7738f5488ee_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet →
        HasPlanarDrawingOn N → N = M := by sorry
