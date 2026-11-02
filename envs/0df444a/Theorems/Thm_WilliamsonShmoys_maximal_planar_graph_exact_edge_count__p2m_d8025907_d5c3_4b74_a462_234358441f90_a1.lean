-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:19:49.64056+00:00
-- url     : https://prove2.me/theorems/8c2d67f5-f1e5-4c7d-86ce-91654da8274a
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   A drawable graph on at least three finite vertices that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges. The condition |V| ≥ 3 includes the triangle boundary case and is essential for the planar triangulation count. An independent route is to show maximality makes every face triangular, count edge-face incidences, and combine that count with Euler’s formula. Formalizing faces and Euler’s formula for the supplied continuous-arc drawing definition is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_d8025907_d5c3_4b74_a462_234358441f90_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hn : 3 <= Fintype.card V)
    (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M →
      L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset = L.edgeFinset) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
