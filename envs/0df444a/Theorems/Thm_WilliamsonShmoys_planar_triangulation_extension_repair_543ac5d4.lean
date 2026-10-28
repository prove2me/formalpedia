-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_repair_543ac5d4
-- name    : WilliamsonShmoys.planar_triangulation_extension_repair_543ac5d4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:41:10.924714+00:00
-- url     : https://prove2.me/theorems/ce211951-d132-4f9e-ae3f-ea6e34e477ed
-- title:
--   Drawable maximal planar extension for the repair
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on that same type with exactly `3|V| - 6` edges. Add drawable edges while possible; finiteness gives a maximal planar supergraph, whose faces are triangular and whose edge count follows from Euler's formula. When `|V| = 3`, the extension is the triangle, including when the original graph has fewer edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_repair_543ac5d4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ U : SimpleGraph V,
      G <= U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      3 * Fintype.card V = U.edgeSet.ncard + 6 := by sorry
