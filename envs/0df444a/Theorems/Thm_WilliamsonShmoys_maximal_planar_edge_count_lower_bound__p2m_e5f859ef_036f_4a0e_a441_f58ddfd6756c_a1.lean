-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:04:42.889316+00:00
-- url     : https://prove2.me/theorems/c2eda16e-e381-4c67-86d8-74bdc260bd3a
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge-set extension has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
