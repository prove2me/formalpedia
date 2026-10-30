-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_729fc1e5
-- name    : WilliamsonShmoys.planar_edge_augmentation_729fc1e5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:09:03.082176+00:00
-- url     : https://prove2.me/theorems/65400e4a-a313-4883-aba6-4011eb4fc427
-- title:
--   Augmenting a sparse planar graph
-- statement:
--   A drawable simple graph with at least three vertices and fewer than 3|V|−6 edges has a strict drawable supergraph on the same vertices. The strict deficit hypothesis excludes the equality boundary; a proof route is to extend to a maximal planar supergraph and use face-boundary arguments to find an addable edge unless the embedding is triangulated.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_729fc1e5
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hE : R.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ S : SimpleGraph V, R ≤ S ∧ S ≠ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn S := by
  sorry
