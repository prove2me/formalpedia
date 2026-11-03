-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:41.954508+00:00
-- url     : https://prove2.me/theorems/821cfc5b-ccd1-4ee0-9165-24b74bcf0b03
-- title:
--   Maximal planar drawing has the Euler edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on its vertex set has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (J : SimpleGraph V), H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := dH;
      H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
