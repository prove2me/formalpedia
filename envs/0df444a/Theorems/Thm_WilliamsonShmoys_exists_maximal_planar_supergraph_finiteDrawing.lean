-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finiteDrawing
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finiteDrawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:55:34.008686+00:00
-- url     : https://prove2.me/theorems/054e092a-3fc9-40f3-8d40-7a594483c458
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   A drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finiteDrawing {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U) (hV : 3 ≤ Fintype.card V) : ∃ W : SimpleGraph V, U ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W := by sorry
