-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_from_drawing_20261027
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_from_drawing_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:28:23.484203+00:00
-- url     : https://prove2.me/theorems/e9dfd49a-0826-4bab-8e34-06ce398808bd
-- title:
--   Planar drawing edge count upper bound from drawing
-- statement:
--   Every graph with a planar drawing on at least three vertices has at most 3|V|−6 edges. For |V| = 3 this is the bound of three edges. The lemma removes the universal planar upper-bound step from the target. A proof route is to add noncrossing edges on the same vertex set until the drawing is triangulated, apply Euler’s formula and face-edge incidence counting, and use that the original edge set is included in the augmented one. The remaining work is formalizing the augmentation and count from HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_from_drawing_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
