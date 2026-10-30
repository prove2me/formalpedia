-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1
-- name    : WilliamsonShmoys.planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:15:25.162981+00:00
-- url     : https://prove2.me/theorems/731c5de7-e12c-4abd-b3d4-d772f92e7121
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly three times the number of vertices minus six edges. The completion argument must also cover disconnected starting graphs and the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_cardinality__p2m_e15f7e2c_ce0e_4996_9963_e731b96f551d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
