-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:03:20.173272+00:00
-- url     : https://prove2.me/theorems/429266ef-2658-4bcb-86f5-df3246663c92
-- title:
--   A maximal drawable graph on at least three vertices has 3n−6 edges
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ff749fca_dc51_4e6e_b241_1d544557ca96_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) (hmax : ∀ W : SimpleGraph V, Z ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = Z) : Z.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
