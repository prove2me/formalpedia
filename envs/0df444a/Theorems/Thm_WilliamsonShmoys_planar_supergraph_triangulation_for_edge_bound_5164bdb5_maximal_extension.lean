-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_extension
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:53:29.086054+00:00
-- url     : https://prove2.me/theorems/1ebf83c0-5c6c-4d2c-b57e-7034b6e4861c
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Extend the given drawing to a planar supergraph on the same finite vertex set that is maximal among planar supergraphs. The condition `|V| ≥ 3` is retained for the subsequent edge-count theorem; disconnected graphs and isolated vertices are allowed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

theorem WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
