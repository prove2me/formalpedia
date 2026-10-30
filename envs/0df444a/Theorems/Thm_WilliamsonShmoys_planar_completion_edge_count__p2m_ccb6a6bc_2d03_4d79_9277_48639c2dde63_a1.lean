-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:59:15.032109+00:00
-- url     : https://prove2.me/theorems/1d9e4996-f1da-4af7-951a-5adb0b1eb381
-- title:
--   Completion of a drawable graph to the planar edge count
-- statement:
--   Every drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertices having exactly 3|V| − 6 edges. The child packages the finite planar augmentation and Euler-counting argument; the parent uses maximality to show that this completion equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_ccb6a6bc_2d03_4d79_9277_48639c2dde63_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) : ∃ P : SimpleGraph V, Set.Subset N.edgeSet P.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn P ∧ P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
