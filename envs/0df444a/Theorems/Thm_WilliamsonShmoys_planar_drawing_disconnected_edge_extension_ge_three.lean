-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_edge_extension_ge_three
-- name    : WilliamsonShmoys.planar_drawing_disconnected_edge_extension_ge_three
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:02:06.195147+00:00
-- url     : https://prove2.me/theorems/bdfb3ab0-aa17-4bd8-8916-bea0d0455c36
-- title:
--   Planar edge augmentation for disconnected drawn graphs with at least three vertices
-- statement:
--   A disconnected graph on at least three vertices with the specified planar drawing has a planar supergraph on the same vertices that is not a subgraph of the original graph. The geometric argument is to re-embed separate components in disjoint regions and connect them by a new edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_edge_extension_ge_three
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ¬ K ≤ H := by
  sorry
