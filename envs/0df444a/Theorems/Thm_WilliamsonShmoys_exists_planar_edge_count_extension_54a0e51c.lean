-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_count_extension_54a0e51c
-- name    : WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:15:50.564363+00:00
-- url     : https://prove2.me/theorems/f56d394a-03d3-402d-8d6f-651f25ea859b
-- title:
--   Planar extension with maximal edge count
-- statement:
--   Every finite drawable graph on at least three vertices extends, on the same vertex set, to a drawable graph with exactly `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_edge_count_extension_54a0e51c
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
