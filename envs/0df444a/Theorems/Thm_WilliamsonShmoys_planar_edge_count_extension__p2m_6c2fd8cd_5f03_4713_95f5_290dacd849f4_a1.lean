-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1
-- name    : WilliamsonShmoys.planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:03:50.628083+00:00
-- url     : https://prove2.me/theorems/efe3e864-4fbd-4f0b-a1f2-70ba02623cb8
-- title:
--   Planar edge-count extension
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This removes the parent’s maximality hypothesis: once the parent applies its maximality condition to this extension, the extension equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_extension__p2m_6c2fd8cd_5f03_4713_95f5_290dacd849f4_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
