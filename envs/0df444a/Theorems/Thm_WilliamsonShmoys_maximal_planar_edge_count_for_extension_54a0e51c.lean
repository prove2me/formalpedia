-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_extension_54a0e51c
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_extension_54a0e51c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:46:03.669194+00:00
-- url     : https://prove2.me/theorems/212ca197-4074-4d9a-b46d-ee46c950e228
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices with no drawable strict supergraph has exactly `3n − 6` edges. The independent proof route is to show maximality forces every face to be triangular, then combine Euler’s formula with face-edge incidence counting. The lower bound on the vertex count is required for this edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_extension_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet ⊆ L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
