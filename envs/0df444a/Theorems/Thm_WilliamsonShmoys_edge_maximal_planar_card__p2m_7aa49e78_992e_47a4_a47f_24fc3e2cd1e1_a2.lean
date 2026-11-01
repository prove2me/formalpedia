-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- name    : WilliamsonShmoys.edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:53.100204+00:00
-- url     : https://prove2.me/theorems/26401141-9acd-45a7-9799-c63f2391b494
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices with no drawable edge supergraph having additional edges has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_card__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    (∀ H : SimpleGraph V,
      G.edgeFinset ⊆ H.edgeFinset →
      HasPlanarDrawingOn H →
      H.edgeFinset ⊆ G.edgeFinset) →
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
