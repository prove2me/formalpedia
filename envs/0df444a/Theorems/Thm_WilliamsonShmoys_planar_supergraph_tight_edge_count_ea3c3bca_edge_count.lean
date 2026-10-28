-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_tight_edge_count_ea3c3bca_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:36:52.70471+00:00
-- url     : https://prove2.me/theorems/d357ae52-745c-4b5b-a849-2767522cac40
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex set has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_tight_edge_count_ea3c3bca_edge_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) (hcard : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
