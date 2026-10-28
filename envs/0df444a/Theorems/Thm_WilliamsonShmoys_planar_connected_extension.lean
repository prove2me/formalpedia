-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension
-- name    : WilliamsonShmoys.planar_connected_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:45:06.949538+00:00
-- url     : https://prove2.me/theorems/db324782-c561-499c-9a61-9d772f4e7760
-- title:
--   A planar drawing can be extended to a connected planar supergraph
-- statement:
--   On the same finite vertex type, any graph with the stated crossing-free drawing has a connected planar supergraph containing all its edges. Its edge count is at least the original edge count. The condition of at least three vertices is retained for direct use by the connected edge-bound lemma. A proof can add an arc between two distinct components through the complement of the drawing, repeat until connected, and use edge inclusion for the cardinality inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      N.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
