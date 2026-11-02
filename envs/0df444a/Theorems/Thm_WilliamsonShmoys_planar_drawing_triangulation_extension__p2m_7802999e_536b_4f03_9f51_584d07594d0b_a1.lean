-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:35.279663+00:00
-- url     : https://prove2.me/theorems/b901b325-be9f-472f-92a1-3f9f2725a3e6
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_7802999e_536b_4f03_9f51_584d07594d0b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
       M.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
