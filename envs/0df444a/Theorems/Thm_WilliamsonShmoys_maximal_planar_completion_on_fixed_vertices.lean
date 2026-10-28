-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_on_fixed_vertices
-- name    : WilliamsonShmoys.maximal_planar_completion_on_fixed_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:37:59.639992+00:00
-- url     : https://prove2.me/theorems/5000a3d3-511e-405f-b32a-6b656cf08b5b
-- title:
--   Triangulated planar completion on fixed vertices
-- statement:
--   Every graph with a crossing-free drawing on at least three finite ordered vertices can be extended, using the same vertices, to a crossing-free graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ X : SimpleGraph V,
      G ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
