-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:10:24.260207+00:00
-- url     : https://prove2.me/theorems/bd652ef6-f935-4766-81fb-919843a61889
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_444bbc12_374a_443e_a15d_6bd6256fef03_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) (hYmax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z = Y) : Y.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
