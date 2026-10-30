-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:34:01.422792+00:00
-- url     : https://prove2.me/theorems/ef21e4d0-72a9-49ba-9f8c-1146d558edeb
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices that has a planar drawing and admits no drawable edge extension has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4d9c8971_4afd_47f0_9ee2_860519fd763e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 <= Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ u v, u ≠ v → ¬ T.Adj u v →
      ¬ ∃ U : SimpleGraph V,
        (∀ x y, T.Adj x y → U.Adj x y) ∧
        HasPlanarDrawingOn U ∧ U.Adj u v) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
