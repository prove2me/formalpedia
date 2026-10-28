-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_v2_aux
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_v2_aux
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:16:12.151306+00:00
-- url     : https://prove2.me/theorems/d2317296-95b2-49ef-a072-c82d53c5286c
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph with no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_v2_aux
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      (∀ (X : SimpleGraph V), WilliamsonShmoys.HasPlanarDrawingOn X →
        (∀ {u v}, W.Adj u v → X.Adj u v) → X = W) := by sorry
