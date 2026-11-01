-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:27:12.76598+00:00
-- url     : https://prove2.me/theorems/1a017428-1a43-436d-9208-530136878881
-- title:
--   Count the edges of an inclusion-maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite ordered vertices that is inclusion-maximal among drawable supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_bc038eff_dd8d_4b01_9048_8ba39788938c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      (forall {u v : V}, L.Adj u v -> M.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      (forall {u v : V}, M.Adj u v -> L.Adj u v)) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
