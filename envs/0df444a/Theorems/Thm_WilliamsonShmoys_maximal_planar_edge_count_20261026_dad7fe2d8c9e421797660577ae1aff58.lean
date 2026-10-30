-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58
-- name    : WilliamsonShmoys.maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:22:59.234262+00:00
-- url     : https://prove2.me/theorems/94606745-9b57-4243-8db0-1829afcaec6c
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_20261026_dad7fe2d8c9e421797660577ae1aff58
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall K' : SimpleGraph V, K <= K' ->
      WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
