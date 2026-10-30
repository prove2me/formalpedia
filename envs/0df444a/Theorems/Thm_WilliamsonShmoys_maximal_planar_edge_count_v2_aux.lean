-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_v2_aux
-- name    : WilliamsonShmoys.maximal_planar_edge_count_v2_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:21:00.655672+00:00
-- url     : https://prove2.me/theorems/1386dcc6-262c-4636-a36f-17e228af0d00
-- title:
--   Count the edges of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_v2_aux
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ (X : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn X →
      (∀ {u v}, W.Adj u v → X.Adj u v) → X = W) :
    W.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
