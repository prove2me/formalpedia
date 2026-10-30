-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_on_vertices
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_on_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:05:42.211053+00:00
-- url     : https://prove2.me/theorems/1d378649-d46c-4ed0-be34-8f4c2a046230
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices with no drawable strict supergraph on the same vertex set has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_on_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
