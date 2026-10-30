-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:32:27.105308+00:00
-- url     : https://prove2.me/theorems/0edcc40e-6850-49bc-8dd7-6d053c5782bf
-- title:
--   Triangulation extension of a drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_triangulation_extension__p2m_059077c0_2625_4e05_919b_c819570c30dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hS : HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
