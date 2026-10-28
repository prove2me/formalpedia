-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- name    : WilliamsonShmoys.maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:32:37.871754+00:00
-- url     : https://prove2.me/theorems/0101a73b-deed-4e60-8961-6588c8e83a6c
-- title:
--   Maximal drawable subgraphs have equal edge sets
-- statement:
--   If S is maximal among drawable graphs and T is a drawable supergraph of S on the same finite vertex type, then S and T have equal edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_subgraph_edgeSet_eq__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S T : SimpleGraph V)
    (hST : ∀ u v, S.Adj u v → T.Adj u v)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ U : SimpleGraph V,
      (∀ u v, S.Adj u v → U.Adj u v) →
      HasPlanarDrawingOn U →
      ∀ u v, U.Adj u v → S.Adj u v) :
    S.edgeSet.ncard = T.edgeSet.ncard := by sorry
