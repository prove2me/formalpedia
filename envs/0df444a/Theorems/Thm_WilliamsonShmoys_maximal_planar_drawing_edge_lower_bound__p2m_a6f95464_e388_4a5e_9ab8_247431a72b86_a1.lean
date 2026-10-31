-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:15.157376+00:00
-- url     : https://prove2.me/theorems/6c0b32fd-3010-4944-8a0a-c5032f66ed7a
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   An inclusion maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. In a maximal drawing every face is triangular (including the cases handled by the planar embedding argument); counting face-edge incidences together with Euler’s formula yields the edge bound. This child carries the main topological and planar counting work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
