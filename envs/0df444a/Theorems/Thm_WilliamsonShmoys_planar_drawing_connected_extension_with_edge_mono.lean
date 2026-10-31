-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_with_edge_mono
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:50:13.108294+00:00
-- url     : https://prove2.me/theorems/26526fc0-7365-41e0-9070-d01ed12641ac
-- title:
--   Connect a finite planar drawing without decreasing its edge count
-- statement:
--   A finite graph with the supplied planar drawing and at least three vertices can be extended on the same vertex type to a connected graph with a planar drawing, without decreasing its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧ Z.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
        Y.edgeSet.ncard ≤ Z.edgeSet.ncard := by sorry
