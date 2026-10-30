-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_extension_maximal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_extension_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:36:29.866385+00:00
-- url     : https://prove2.me/theorems/acf9845a-f5b6-4dcb-a2de-f4fd98117e90
-- title:
--   An inclusion-maximal planar graph has 3n−6 edges
-- statement:
--   An inclusion-maximal planar simple graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_extension_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M <= L)
    (hV : 3 <= Fintype.card V) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
