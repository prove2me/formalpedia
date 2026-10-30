-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:27:29.743533+00:00
-- url     : https://prove2.me/theorems/89e15e62-22ba-485e-a799-1c4e4aebe35a
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal graph admitting the specified planar drawing, on at least three vertices, has exactly `3 * |V| - 6` edges. The proof route is to establish that maximality forces triangular faces, count face-edge incidences, and apply Euler’s formula; small cases are excluded by the cardinality hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (∀ u v, H.Adj u v → K.Adj u v) →
      ∀ u v, K.Adj u v → H.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
