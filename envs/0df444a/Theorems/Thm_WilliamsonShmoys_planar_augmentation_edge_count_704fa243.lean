-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_edge_count_704fa243
-- name    : WilliamsonShmoys.planar_augmentation_edge_count_704fa243
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:40:06.65491+00:00
-- url     : https://prove2.me/theorems/9d7024b9-8679-45be-8cb9-713a0163930a
-- title:
--   Planar augmentation with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3n−6 edges. The condition n≥3 covers the triangular boundary case; the claim follows by augmenting to a maximal planar embedding, showing its faces are triangles, and applying Euler’s formula with edge-face incidence counting. This removes the planar-topology and counting work from the parent. The remaining core obligation is to formalize that augmentation and triangulation argument for the supplied continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_edge_count_704fa243
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
