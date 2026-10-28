-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_via_faces
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_via_faces
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:32:41.6459+00:00
-- url     : https://prove2.me/theorems/589bf4c0-c4be-43fb-a487-9eff2c55fee4
-- title:
--   Count edges of an inclusion-maximal drawable graph by faces
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges. The vertex lower bound excludes the small cases where this formula need not hold. Prove it by showing maximality forces a triangulation and applying Euler’s formula and face-edge incidence counting; that topological argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_via_faces
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
