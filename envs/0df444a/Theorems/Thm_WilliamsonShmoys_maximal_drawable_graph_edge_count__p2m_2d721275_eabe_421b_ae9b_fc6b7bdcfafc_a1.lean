-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:51.186145+00:00
-- url     : https://prove2.me/theorems/cc05e90a-af6b-4557-980d-9087018dc646
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to show every face of a maximal planar drawing is triangular, then combine the triangular-face count with Euler’s formula and convert the resulting edge-set cardinality to edgeFinset.card.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_2d721275_eabe_421b_ae9b_fc6b7bdcfafc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
