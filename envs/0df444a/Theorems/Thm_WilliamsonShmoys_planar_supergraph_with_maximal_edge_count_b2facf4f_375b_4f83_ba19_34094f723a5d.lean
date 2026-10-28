-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d
-- name    : WilliamsonShmoys.planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:37:16.036394+00:00
-- url     : https://prove2.me/theorems/ec05fb32-d087-4cea-a2cd-8a3ca91ed513
-- title:
--   Planar completion with maximal edge count
-- statement:
--   Any finite drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_maximal_edge_count_b2facf4f_375b_4f83_ba19_34094f723a5d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
