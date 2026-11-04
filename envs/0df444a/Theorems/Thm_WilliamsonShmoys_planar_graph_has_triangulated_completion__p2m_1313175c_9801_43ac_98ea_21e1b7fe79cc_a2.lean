-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
-- name    : WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:48.081939+00:00
-- url     : https://prove2.me/theorems/76432751-4a60-438b-af25-c322d55d602e
-- title:
--   Planar graph triangulated completion
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex set, to a triangulated planar graph whose edge count is exactly three times the number of vertices minus six. This completion implies the target by monotonicity of edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_graph_has_triangulated_completion__p2m_1313175c_9801_43ac_98ea_21e1b7fe79cc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, ∃ (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       G.edgeFinset ⊆ H.edgeFinset ∧
         H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
