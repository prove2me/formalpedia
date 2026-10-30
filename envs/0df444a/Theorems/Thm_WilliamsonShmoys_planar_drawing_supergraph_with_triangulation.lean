-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_with_triangulation
-- name    : WilliamsonShmoys.planar_drawing_supergraph_with_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:59:53.574867+00:00
-- url     : https://prove2.me/theorems/71ca74e3-59b7-4c87-a300-05b65c7d4715
-- title:
--   Planar drawings admit triangulated supergraphs
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges. Such a supergraph is obtained by triangulating the faces of a planar embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_supergraph_with_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V,
      LE.le Z W ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      3 * Fintype.card V - 6 = W.edgeSet.ncard := by sorry
