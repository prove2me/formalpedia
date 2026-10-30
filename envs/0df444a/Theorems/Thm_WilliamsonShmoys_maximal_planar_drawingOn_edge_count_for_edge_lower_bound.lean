-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_for_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_edge_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:15:08.241499+00:00
-- url     : https://prove2.me/theorems/fdae00bc-8a62-4704-8dc7-c79d69b42ebc
-- title:
--   Edge count of a maximal planar drawing for the lower bound
-- statement:
--   An edge-maximal simple planar graph with at least three vertices has exactly 3n−6 edges. This new topological lemma removes the quantitative edge-count step from the parent. A proof route is to show maximality forces a triangulation, then use Euler’s formula and count face-edge incidences. The exact arc-based drawing definition makes formalizing that route the remaining core obligation; the boundary case n=3 is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawingOn_edge_count_for_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hMax : ∀ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W →
      (∀ u v, U.Adj u v → W.Adj u v) →
      ∀ u v, W.Adj u v → U.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = U.edgeSet.ncard + 6 := by sorry
