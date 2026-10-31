-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:36.354613+00:00
-- url     : https://prove2.me/theorems/0b1d558b-5b99-484a-a69e-3ba1af67a959
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A connected, inclusion-maximal drawable simple graph with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_303ddd52_95e9_4125_a752_478be76ea7a5_a1
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hconn : T.Connected)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ S : SimpleGraph V, T ≤ S → HasPlanarDrawingOn S → S = T) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
