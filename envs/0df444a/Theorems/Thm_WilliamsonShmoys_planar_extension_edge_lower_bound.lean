-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_lower_bound
-- name    : WilliamsonShmoys.planar_extension_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:52:17.306764+00:00
-- url     : https://prove2.me/theorems/b1d37ed7-139d-47d2-911f-7f37e908571b
-- title:
--   Planar augmentation reaches the maximal planar edge bound
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with at least 3|V|-6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      (∀ ⦃u v⦄, K.Adj u v → M.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
