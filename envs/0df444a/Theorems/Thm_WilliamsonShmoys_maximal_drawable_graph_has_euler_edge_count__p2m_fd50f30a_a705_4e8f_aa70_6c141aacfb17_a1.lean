-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:18:44.297207+00:00
-- url     : https://prove2.me/theorems/fc02047b-ad3c-4a9e-81a3-7d77431738b5
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable edge extension on that vertex set has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_fd50f30a_a705_4e8f_aa70_6c141aacfb17_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      (forall u v, M.Adj u v -> N.Adj u v) ->
      HasPlanarDrawingOn N ->
      forall u v, N.Adj u v -> M.Adj u v) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = M.edgeFinset.card := by sorry
