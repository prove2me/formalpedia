-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:49.191821+00:00
-- url     : https://prove2.me/theorems/88a12398-1857-4cda-a49a-bb014d1d3fb8
-- title:
--   Edge lower bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite ordered vertices has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_74da5e6a_674d_4f79_986e_ea1a1f3184a0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall N : SimpleGraph V,
      (forall {u v : V}, M.Adj u v -> N.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     3 * Fintype.card V - 6 <= M.edgeFinset.card) := by sorry
