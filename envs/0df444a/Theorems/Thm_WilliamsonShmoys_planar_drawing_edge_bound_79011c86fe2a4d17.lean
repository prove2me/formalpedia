-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_79011c86fe2a4d17
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_79011c86fe2a4d17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:34:16.143747+00:00
-- url     : https://prove2.me/theorems/4ee683cc-4060-4246-bc37-9b79b9d4a264
-- title:
--   Edge bound for a planar drawing
-- statement:
--   Every graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_79011c86fe2a4d17
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
