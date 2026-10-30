-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:35:39.294267+00:00
-- url     : https://prove2.me/theorems/001a49a0-362a-4308-9ab6-2c7f670346c3
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A drawable simple graph on at least three vertices that admits no proper drawable supergraph has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_bbef08b9_09b8_4a50_88ab_5b845e32b992_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
