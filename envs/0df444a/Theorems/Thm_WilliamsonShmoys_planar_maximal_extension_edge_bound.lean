-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_edge_bound
-- name    : WilliamsonShmoys.planar_maximal_extension_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:29:00.020103+00:00
-- url     : https://prove2.me/theorems/dd6702e8-a499-471f-9f84-a1c25128cff1
-- title:
--   Planar extension with the maximal planar edge bound
-- statement:
--   Any graph on at least three vertices with the specified crossing-free drawing has a planar supergraph on the same vertex set with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
