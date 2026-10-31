-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:22.539398+00:00
-- url     : https://prove2.me/theorems/3bdd09ac-e2e3-4767-b598-2a6e24b78964
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal finite simple planar graph with at least three vertices has at least `3n−6` edges. This removes the general upper-bound work from the parent and focuses on the effect of maximality. A proof route is to use planar augmentation to show the drawing’s graph is connected and every face is triangular, then count face-edge incidences and apply Euler’s formula. The `n=3` boundary is covered: maximality forces all three possible edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
