-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:59:42.679134+00:00
-- url     : https://prove2.me/theorems/f5dec54e-fcbf-4bab-a342-af462107c326
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_558e4c7b_93a1_4c08_9af2_8975677e8b56_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
