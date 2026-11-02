-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:45:36.129716+00:00
-- url     : https://prove2.me/theorems/08c24848-031b-43ea-aa26-092fb49494c8
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   Any graph on at least three vertices that has a `HasPlanarDrawingOn` drawing and is maximal among planar supergraphs on the same vertex set has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → HasPlanarDrawingOn N → N = M) :
    (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
