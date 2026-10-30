-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:57:07.853585+00:00
-- url     : https://prove2.me/theorems/1bca9e8d-9b62-4fe4-94af-9f67da983417
-- title:
--   An inclusion maximal planar graph has the maximal planar edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge-set inclusion has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_731c5de7_e12c_4abd_b3d4_d772f92e7121_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet →
      HasPlanarDrawingOn N → Set.Subset N.edgeSet M.edgeSet) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
