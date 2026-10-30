-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:30:34.55365+00:00
-- url     : https://prove2.me/theorems/98c8bf31-da7f-4753-99f2-642509315647
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
