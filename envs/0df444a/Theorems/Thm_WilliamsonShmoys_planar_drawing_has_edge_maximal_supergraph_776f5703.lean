-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph_776f5703
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_776f5703
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:06:07.934365+00:00
-- url     : https://prove2.me/theorems/c665ec32-d3b7-4405-8d78-dba2e3082ec6
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph_776f5703 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
