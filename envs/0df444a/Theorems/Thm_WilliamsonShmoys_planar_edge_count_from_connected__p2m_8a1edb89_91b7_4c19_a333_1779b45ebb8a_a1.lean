-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
-- name    : WilliamsonShmoys.planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:48.815788+00:00
-- url     : https://prove2.me/theorems/7851b0dc-47ad-49a3-a8e3-cfe708bc6902
-- title:
--   Reduce the planar edge bound to connected drawings
-- statement:
--   If every connected simple graph on this same finite ordered vertex type with a planar drawing and at least three vertices satisfies the edge bound, then every graph with a planar drawing on the type satisfies it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_from_connected__p2m_8a1edb89_91b7_4c19_a333_1779b45ebb8a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconnBound : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H.Connected → HasPlanarDrawingOn H → 3 ≤ Fintype.card V →
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6))
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
