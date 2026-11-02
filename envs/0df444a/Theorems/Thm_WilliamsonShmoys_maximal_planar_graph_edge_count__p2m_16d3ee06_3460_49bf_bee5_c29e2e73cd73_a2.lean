-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:40:29.288395+00:00
-- url     : https://prove2.me/theorems/077d3f0d-ff79-48f3-bde0-954cbd7dcf68
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal simple graph admitting the specified planar drawing, with at least three vertices, has exactly 3n - 6 edges. The proof route is to establish connectedness and triangular faces, then apply Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_16d3ee06_3460_49bf_bee5_c29e2e73cd73_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V, HasPlanarDrawingOn J → H ≤ J → J = H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
