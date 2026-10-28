-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_component_merge
-- name    : WilliamsonShmoys.planar_drawing_component_merge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:40:29.708146+00:00
-- url     : https://prove2.me/theorems/4c0ffef1-df07-4b75-a606-88ee2ca13553
-- title:
--   Planar extension that merges components
-- statement:
--   A disconnected finite graph with at least three vertices and a planar drawing has a planar supergraph on the same vertices with fewer connected components. The proof must produce a drawing of the enlarged graph, potentially by redrawing the original components before joining two of them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_component_merge
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hDisconnected : ¬ Y.Connected)
    (iY : Fintype Y.ConnectedComponent) :
    ∃ (Z : SimpleGraph V), ∃ (iZ : Fintype Z.ConnectedComponent),
      Y ≤ Z ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
        @Fintype.card Z.ConnectedComponent iZ <
          @Fintype.card Y.ConnectedComponent iY := by sorry
