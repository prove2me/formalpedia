-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:28.060215+00:00
-- url     : https://prove2.me/theorems/1ac9c334-525d-486c-82db-79a23d6eb9e0
-- title:
--   Extend a planar drawing to an edge-maximal planar graph
-- statement:
--   Every finite planar graph on at least three vertices has an edge-maximal planar supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V,
      N.edgeSet.ncard <= M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ M' : SimpleGraph V, M <= M' →
        WilliamsonShmoys.HasPlanarDrawingOn M' → M' = M) := by
  sorry
