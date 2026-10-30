-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_to_edge_bound
-- name    : WilliamsonShmoys.planar_augmentation_to_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:53:27.14599+00:00
-- url     : https://prove2.me/theorems/f07ae698-e6ae-4ab6-9298-6501102dcc32
-- title:
--   Planar augmentation reaches the triangulation edge count
-- statement:
--   Any crossing-free drawing on at least three vertices can be extended, on the same vertex set, to a crossing-free drawing whose graph has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_to_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      G.edgeSet ⊆ S.edgeSet ∧
      S.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
