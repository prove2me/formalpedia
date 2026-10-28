-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_planar_supergraph
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_planar_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:20:02.755813+00:00
-- url     : https://prove2.me/theorems/393af010-a607-4197-ad6d-7e2bc28c0d48
-- title:
--   Triangulate a planar drawing on the same vertex set
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing can be extended, on the same vertex set, to a crossing-free simple graph with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
