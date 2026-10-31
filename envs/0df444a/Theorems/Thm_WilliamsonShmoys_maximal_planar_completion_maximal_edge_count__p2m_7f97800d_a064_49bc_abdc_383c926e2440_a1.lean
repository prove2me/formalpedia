-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:32.442907+00:00
-- url     : https://prove2.me/theorems/078165f8-2282-4c2b-9ab6-7e9aed87e1a3
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph that is maximal under drawable edge extensions has exactly `3|V|−6` edges when it has at least three vertices. This isolates the connectivity, face triangulation, and Euler-count argument from the construction of a maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hmaximal : forall N : SimpleGraph V, LE.le M N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) (hV : 3 <= Fintype.card V) : M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
