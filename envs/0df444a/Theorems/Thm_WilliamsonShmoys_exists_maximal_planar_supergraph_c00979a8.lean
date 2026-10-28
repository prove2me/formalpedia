-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_c00979a8
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:14:58.101127+00:00
-- url     : https://prove2.me/theorems/b0331c4f-6b2f-4898-9f8b-0ccdf22209b1
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph maximal among drawable supergraphs on that same type. The extension contains the original graph, so it has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ L : SimpleGraph V, H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H) ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
