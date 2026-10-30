-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:53:52.100864+00:00
-- url     : https://prove2.me/theorems/e5f859ef-036f-4a0e-a441-f58ddfd6756c
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that is maximal under drawable edge-set extension has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_0fb24e84_44a0_421e_a186_c4879c0fa6ba_a1 {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
