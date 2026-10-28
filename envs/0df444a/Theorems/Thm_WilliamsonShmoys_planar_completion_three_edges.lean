-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_three_edges
-- name    : WilliamsonShmoys.planar_completion_three_edges
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:32:39.59588+00:00
-- url     : https://prove2.me/theorems/d02dec5c-46dc-48a3-a22b-812ae758970e
-- title:
--   Drawable completion to a triangulation
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_three_edges
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
