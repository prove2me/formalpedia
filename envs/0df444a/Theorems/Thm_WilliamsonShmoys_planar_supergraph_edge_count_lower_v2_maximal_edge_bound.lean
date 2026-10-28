-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_count_lower_v2_maximal_edge_bound
-- name    : WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:28:57.965295+00:00
-- url     : https://prove2.me/theorems/d34194a3-ebe5-43bf-8ceb-613350147597
-- title:
--   An inclusion-maximal drawable graph has the planar edge lower bound
-- statement:
--   An inclusion-maximal graph with a drawing witness has at least $3|V|-6$ edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_count_lower_v2_maximal_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N → M ≤ N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 <= (M.edgeSet.ncard : Int) := by sorry
