-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:33.718363+00:00
-- url     : https://prove2.me/theorems/af8ffdb6-a3ca-4deb-99d5-c1621ba2f570
-- title:
--   Drawable graphs have a triangulated completion
-- statement:
--   Any drawable simple graph on at least three vertices is a subgraph of a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulation_completion__p2m_5ea12a57_b3bb_4923_a983_804aaa92fdce_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
        3 * Fintype.card V = M.edgeFinset.card + 6) := by sorry
