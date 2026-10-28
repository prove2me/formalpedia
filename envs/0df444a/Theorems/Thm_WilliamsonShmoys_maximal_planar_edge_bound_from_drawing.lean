-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_from_drawing
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:39:40.130437+00:00
-- url     : https://prove2.me/theorems/6c2b7c10-a8c6-43bc-a680-bed4e9a9961b
-- title:
--   A maximal drawable graph has at least the planar edge bound
-- statement:
--   Every inclusion-maximal drawable simple graph on at least three vertices has at least $3|V|-6$ edges. Maximality forces a connected triangulation (with the three-vertex boundary handled directly), after which Euler’s formula yields the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hNmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
