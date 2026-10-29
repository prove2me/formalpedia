-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound_for_supergraph_completion
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound_for_supergraph_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:17:33.113989+00:00
-- url     : https://prove2.me/theorems/b9f04a05-a438-43ae-a2ca-730f23ec6864
-- title:
--   Edge bound for a maximal drawable graph in a supergraph completion
-- statement:
--   An inclusion-maximal graph drawable on a finite vertex type with at least three vertices has at least $3|V|-6$ edges. This isolates the topological work: show maximality forces a triangulation, or otherwise enough edges, and apply Euler's formula. The size hypothesis is needed; this statement preserves it explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound_for_supergraph_completion {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) : 3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
