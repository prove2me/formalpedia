-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_for_edge_count
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:29:39.330083+00:00
-- url     : https://prove2.me/theorems/cb2e894b-f230-44ae-8141-f3da2b1a27f5
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every planar simple graph on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ J : SimpleGraph V, H.edgeSet ⊆ J.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ ∀ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K → J.edgeSet ⊆ K.edgeSet → K.edgeSet = J.edgeSet := by sorry
