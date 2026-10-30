-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- name    : WilliamsonShmoys.planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:04:37.162006+00:00
-- url     : https://prove2.me/theorems/d834da15-b585-41bf-a8ee-e18eb971234e
-- title:
--   Existence of a maximal planar supergraph on the same vertices
-- statement:
--   Every finite drawable graph on a linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs by edge inclusion. It contains the original edge set, so its edge count is at least as large. The statement also assumes at least three vertices, matching the target’s hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_maximalSupergraph__p2m_998ffb22_8369_4943_b685_9f335822785c_a1 {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      M.edgeSet.ncard ≤ T.edgeSet.ncard ∧
      M.edgeSet ⊆ T.edgeSet ∧
      HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T.edgeSet ⊆ U.edgeSet →
        HasPlanarDrawingOn U → U.edgeSet ⊆ T.edgeSet := by
  sorry
