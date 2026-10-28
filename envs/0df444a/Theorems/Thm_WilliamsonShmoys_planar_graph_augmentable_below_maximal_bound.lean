-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentable_below_maximal_bound
-- name    : WilliamsonShmoys.planar_graph_augmentable_below_maximal_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:42:32.255552+00:00
-- url     : https://prove2.me/theorems/eeac03ef-36e6-44d1-be88-71ee042c1f55
-- title:
--   Sparse drawable graphs admit a drawable edge augmentation
-- statement:
--   Every drawable simple graph on at least three vertices with fewer than 3n − 6 edges has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_graph_augmentable_below_maximal_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hsparse : K.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ L : SimpleGraph V, K <= L ∧ K ≠ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
