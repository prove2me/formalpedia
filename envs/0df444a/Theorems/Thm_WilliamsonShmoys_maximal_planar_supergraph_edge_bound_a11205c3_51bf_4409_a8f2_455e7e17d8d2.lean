-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_bound_a11205c3_51bf_4409_a8f2_455e7e17d8d2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_bound_a11205c3_51bf_4409_a8f2_455e7e17d8d2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:36:46.637389+00:00
-- url     : https://prove2.me/theorems/6e31f1f9-6b57-4c6d-969e-fc2eb5bff20f
-- title:
--   An edge-maximal planar graph meets the triangulation lower bound
-- statement:
--   A planar graph on at least three vertices with no proper planar supergraph on the same vertices has at least \(3n-6\) edges. The intended route is to establish connectedness and triangular faces from maximality, then apply Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_bound_a11205c3_51bf_4409_a8f2_455e7e17d8d2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      (∀ ⦃u v : V⦄, L.Adj u v → K.Adj u v)) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
