-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- name    : WilliamsonShmoys.maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:37.869792+00:00
-- url     : https://prove2.me/theorems/7a506924-211f-41ba-877a-336e51746219
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices whose edge set cannot be strictly enlarged while preserving drawability has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximalPlanar_edgeCount__p2m_998ffb22_8369_4943_b685_9f335822785c_a1 {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (hT : HasPlanarDrawingOn T)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet →
      HasPlanarDrawingOn U → U.edgeSet ⊆ T.edgeSet) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
