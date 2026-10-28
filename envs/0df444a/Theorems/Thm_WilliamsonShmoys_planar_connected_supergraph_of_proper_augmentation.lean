-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_proper_augmentation
-- name    : WilliamsonShmoys.planar_connected_supergraph_of_proper_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:05:51.209325+00:00
-- url     : https://prove2.me/theorems/fc7d862e-3d23-42e4-bf24-1714752d79ee
-- title:
--   Connected planar supergraph from strict planar augmentation
-- statement:
--   If every disconnected planar graph on the fixed finite vertex type has a strict planar supergraph, then every such starting graph P has a connected planar supergraph. Choose an inclusion-maximal planar supergraph containing P from the finite set of graphs on V; the augmentation hypothesis rules out its being disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_of_proper_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hAugment : ∀ G : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn H ∧ G ≤ H ∧ G ≠ H) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected ∧ P ≤ Q := by
  sorry
