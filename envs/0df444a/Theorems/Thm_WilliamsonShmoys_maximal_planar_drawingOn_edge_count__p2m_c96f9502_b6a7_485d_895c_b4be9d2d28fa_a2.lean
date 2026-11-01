-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:24:26.692258+00:00
-- url     : https://prove2.me/theorems/b7392340-665b-4504-a6f8-564aece7c19c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite linearly ordered vertices with no strictly larger drawable supergraph has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count__p2m_c96f9502_b6a7_485d_895c_b4be9d2d28fa_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
