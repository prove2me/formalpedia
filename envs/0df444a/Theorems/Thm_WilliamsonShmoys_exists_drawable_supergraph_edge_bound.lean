-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_edge_bound
-- name    : WilliamsonShmoys.exists_drawable_supergraph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:45:28.358698+00:00
-- url     : https://prove2.me/theorems/bbd2bfc7-9bb4-4e80-a236-486b272cebfd
-- title:
--   Drawable supergraph with the planar edge lower bound
-- statement:
--   Every finite drawable graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This is the same-vertex planar triangulation extension result, stronger than the parent’s maximal-case conclusion. The concrete route is to connect components and add noncrossing edges in faces until the embedding is triangulated, then use Euler’s formula and face-edge incidence counting. It handles the boundary case |V|=3, where the extension is a triangle, and preserves the vertex set and the original edges. This child contains the main remaining topological obligation; it does not follow from Mathlib results found in the pinned source search.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  sorry
