-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:30:31.038785+00:00
-- url     : https://prove2.me/theorems/28855b7d-97e7-45b7-8e9d-f25fb9faa535
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet = L.edgeSet := by sorry
