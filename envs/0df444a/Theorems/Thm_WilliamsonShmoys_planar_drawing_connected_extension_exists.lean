-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:03:25.562412+00:00
-- url     : https://prove2.me/theorems/4b5e3681-b7ca-4f52-a676-3f7a2e2031a4
-- title:
--   Connected planar supergraph extension
-- statement:
--   Every finite graph on at least three ordered vertices with the specified planar drawing has a connected planar supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧ Z.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Z := by sorry
