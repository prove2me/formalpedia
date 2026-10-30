-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:16:59.752885+00:00
-- url     : https://prove2.me/theorems/e2c98e12-54b2-4351-9679-3757ea782119
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that is maximal under drawable edge-set extensions has at least `3n − 6` edges. The standard route is to prove that such an embedding is connected and every face is triangular, then use Euler’s formula; the three-vertex boundary case is the triangle. This isolates the topological and Euler-counting work needed after finite maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      Set.Subset H.edgeSet K.edgeSet →
      H.edgeSet = K.edgeSet)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= H.edgeSet.ncard + 6 := by sorry
