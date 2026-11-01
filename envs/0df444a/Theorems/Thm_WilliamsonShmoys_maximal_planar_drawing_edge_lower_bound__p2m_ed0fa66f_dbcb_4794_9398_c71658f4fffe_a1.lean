-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:16.976431+00:00
-- url     : https://prove2.me/theorems/899b0d31-5122-4616-b662-d79a2f207d1e
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable graphs has at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V, G <= M -> HasPlanarDrawingOn M -> M <= G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      3 * Fintype.card V <= G.edgeFinset.card + 6) := by sorry
