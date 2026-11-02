-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:11:34.64223+00:00
-- url     : https://prove2.me/theorems/f38f8ad9-68a6-4655-b531-6345ea797061
-- title:
--   Reduce the planar edge bound to connected graphs
-- statement:
--   If every connected finite graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices obeys the planar edge bound, then every such finite graph with at least three vertices obeys it, whether connected or not. The reduction must account separately for one-vertex and two-vertex components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hW : 3 <= Fintype.card W)
      (hconn : G.Connected) (hG : HasPlanarDrawingOn G),
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
       G.edgeFinset.card + 6 <= 3 * Fintype.card W)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 <= 3 * Fintype.card V) := by
  sorry
