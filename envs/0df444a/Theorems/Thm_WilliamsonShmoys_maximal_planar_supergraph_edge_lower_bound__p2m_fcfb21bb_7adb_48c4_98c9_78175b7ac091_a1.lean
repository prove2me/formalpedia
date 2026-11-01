-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:13.679325+00:00
-- url     : https://prove2.me/theorems/b575e78e-3e28-4118-93fc-258c931bc299
-- title:
--   A maximal drawable graph reaches the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on those vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V)
    (hMax : forall P : SimpleGraph V,
      (forall {u v : V}, N.Adj u v -> P.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     3 * Fintype.card V - 6 <= N.edgeFinset.card) := by sorry
