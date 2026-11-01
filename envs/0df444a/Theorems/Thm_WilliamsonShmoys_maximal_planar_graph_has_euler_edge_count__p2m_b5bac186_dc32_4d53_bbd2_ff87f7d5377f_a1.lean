-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- name    : WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:37.369593+00:00
-- url     : https://prove2.me/theorems/4ca6b67e-a5cb-47ee-9958-b87be2ab6440
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_graph_has_euler_edge_count__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
