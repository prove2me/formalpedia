-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_20261026
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:26:42.401469+00:00
-- url     : https://prove2.me/theorems/8c088c21-12a7-47e2-a951-9c9df1f35e9f
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple planar graph on at least three vertices that is maximal under edge inclusion has exactly 3|V|−6 edges. Maximality forces a connected triangulation; counting edge-face incidences and applying Euler’s formula yields the stated count. The lower bound includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn J →
      (∀ ⦃u v : V⦄, H.Adj u v → J.Adj u v) → J = H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
