-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_20261026
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_20261026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:21:06.804123+00:00
-- url     : https://prove2.me/theorems/2eb63b94-2ed8-414b-adef-0febe246afd9
-- title:
--   Augmentation below the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a proper drawable supergraph on the same vertex set. A proof route is to extend a finite planar embedding by adding edges within faces until no further edge can be added; the resulting maximal embedding is triangulated, and Euler’s formula gives its edge count. This supplies the contradiction to the parent’s inclusion-maximality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hbelow : M.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ N ≠ M ∧ WilliamsonShmoys.HasPlanarDrawingOn N := by
  sorry
