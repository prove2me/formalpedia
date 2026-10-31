-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:30.98349+00:00
-- url     : https://prove2.me/theorems/8a206f96-b3dd-4ad6-9517-cbf07b9eb0ad
-- title:
--   Every drawable graph has an edge-maximal drawable supergraph
-- statement:
--   Any finite graph with a crossing-free drawing is contained in a graph on the same vertices that is maximal among graphs with such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9a318fe1_85ed_4677_94d2_01eeb5a6121d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ M.edgeSet := by sorry
