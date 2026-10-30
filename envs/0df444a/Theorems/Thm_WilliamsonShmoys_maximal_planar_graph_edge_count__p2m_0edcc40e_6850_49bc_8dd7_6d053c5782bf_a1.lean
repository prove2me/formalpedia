-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:47:00.372926+00:00
-- url     : https://prove2.me/theorems/dd6d4a28-ff1c-4910-81ae-1b1a3100063c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that cannot accept any additional drawable edge has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
