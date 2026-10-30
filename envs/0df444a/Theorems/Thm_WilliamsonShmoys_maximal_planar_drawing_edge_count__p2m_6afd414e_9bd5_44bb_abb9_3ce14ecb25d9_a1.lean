-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:48:06.600979+00:00
-- url     : https://prove2.me/theorems/d4ee878b-f197-42bb-afe9-c773b884d027
-- title:
--   Count the edges of a maximal planar graph
-- statement:
--   A maximal planar simple graph with at least three vertices has exactly $3|V|-6$ edges. The proof route is the classical planar embedding count: maximality forces connectivity and triangular faces; Euler’s formula and double-counting face-edge incidences yield the stated count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6afd414e_9bd5_44bb_abb9_3ce14ecb25d9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
