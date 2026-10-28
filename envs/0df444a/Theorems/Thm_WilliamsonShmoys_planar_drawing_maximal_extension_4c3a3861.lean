-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_4c3a3861
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_4c3a3861
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:48:44.871977+00:00
-- url     : https://prove2.me/theorems/105d007e-cba6-4fb5-b201-9866cb089fc7
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on the same vertices, with at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_4c3a3861
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) := by sorry
