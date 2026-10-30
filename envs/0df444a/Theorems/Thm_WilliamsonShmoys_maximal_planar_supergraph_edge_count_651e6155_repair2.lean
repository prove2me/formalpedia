-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_651e6155_repair2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count_651e6155_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:04:42.773622+00:00
-- url     : https://prove2.me/theorems/b80c2ba3-ac5e-4acb-b2cc-fabf904f1c01
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count_651e6155_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax :
      ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeSet ⊆ N.edgeSet → N.edgeSet = M.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
