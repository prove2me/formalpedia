-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:25.068255+00:00
-- url     : https://prove2.me/theorems/67118cd4-2aed-4d90-82ea-b0a7807bb269
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_f90d547e_0d6a_4173_8130_3021addb1efb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet → HasPlanarDrawingOn K → K.edgeSet = M.edgeSet := by sorry
