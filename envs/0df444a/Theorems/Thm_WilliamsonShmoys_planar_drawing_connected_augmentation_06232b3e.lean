-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_06232b3e
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:04:39.498979+00:00
-- url     : https://prove2.me/theorems/a5a0d303-c713-4ca3-a58e-fe49402e8056
-- title:
--   Connect components of a planar drawing without decreasing the edge count
-- statement:
--   Every finite graph with a planar drawing has a connected planar supergraph on the same vertex type whose edge count is at least the original edge count. This handles disconnected graphs and isolated vertices while preserving the vertex count. The independent proof route is to join drawing components one at a time by arcs in the complement of the existing drawing. The connectedness predicate requires a nonempty vertex type, which follows once the graph has been connected by adding edges; when the original type has one vertex it is already connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_06232b3e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ K.Connected ∧ HasPlanarDrawingOn K ∧
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
