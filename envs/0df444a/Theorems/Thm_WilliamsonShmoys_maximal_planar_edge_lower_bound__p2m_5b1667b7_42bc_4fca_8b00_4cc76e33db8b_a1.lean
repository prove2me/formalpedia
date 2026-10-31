-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:27:59.908443+00:00
-- url     : https://prove2.me/theorems/bc33823c-9eaa-4787-b342-ad6547a0cb58
-- title:
--   Maximal planar simple graphs have at least 3n−6 edges
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. The drawing and maximality hypotheses are both needed: a nonmaximal planar graph may have fewer edges. A proof route augments the drawing on the same vertices to a triangulation, counts its edges, and uses maximality to show the augmentation is the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_5b1667b7_42bc_4fca_8b00_4cc76e33db8b_a1
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
