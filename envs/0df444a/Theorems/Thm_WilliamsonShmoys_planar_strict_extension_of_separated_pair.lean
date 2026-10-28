-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_strict_extension_of_separated_pair
-- name    : WilliamsonShmoys.planar_strict_extension_of_separated_pair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:40:52.663207+00:00
-- url     : https://prove2.me/theorems/79d3406a-7865-422c-8f15-3f14054dab50
-- title:
--   Join two components while preserving planarity
-- statement:
--   If two distinct vertices of a graph are in different components, a planar drawing of the graph can be rearranged to add an edge between them while retaining a planar drawing. This is the substantive geometric augmentation step; the separation premise matters because adding an edge inside a component need not preserve planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_strict_extension_of_separated_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hseparate : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G < H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
