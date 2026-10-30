-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a4
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:04:47.055154+00:00
-- url     : https://prove2.me/theorems/16611d62-0fcd-4179-825c-86d4ca9735c2
-- title:
--   Extend a finite drawable graph to the maximal planar edge count
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing is a subgraph, on the same vertex set, of a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_ef21e4d0_72a9_49ba_9f8c_1146d558edeb_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      (∀ x y, T.Adj x y → U.Adj x y) ∧
      HasPlanarDrawingOn U ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
