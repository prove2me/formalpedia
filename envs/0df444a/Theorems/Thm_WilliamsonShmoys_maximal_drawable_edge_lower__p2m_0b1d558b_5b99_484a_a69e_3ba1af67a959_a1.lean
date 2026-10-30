-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:37:39.971725+00:00
-- url     : https://prove2.me/theorems/7ea2506e-9078-4385-93a6-696ca30b6152
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   A connected drawable graph on at least three vertices that is maximal among drawable graphs on the same vertex set has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_lower__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : T.Connected)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) :
    3 * Fintype.card V - 6 ≤ T.edgeSet.ncard := by sorry
