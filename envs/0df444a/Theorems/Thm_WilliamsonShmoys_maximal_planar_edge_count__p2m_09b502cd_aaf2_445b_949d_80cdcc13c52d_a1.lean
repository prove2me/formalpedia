-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:24:21.390655+00:00
-- url     : https://prove2.me/theorems/9fdf65a3-2cbf-4cec-9951-ee8b977e74bf
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that admits no drawable proper supergraph on the same vertex set has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_09b502cd_aaf2_445b_949d_80cdcc13c52d_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 <= Fintype.card V) (hMax : ∀ N : SimpleGraph V, Set.Subset M.edgeSet N.edgeSet → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
