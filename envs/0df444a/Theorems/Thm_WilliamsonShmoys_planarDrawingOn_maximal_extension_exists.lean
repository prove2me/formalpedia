-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximal_extension_exists
-- name    : WilliamsonShmoys.planarDrawingOn_maximal_extension_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:21:38.395992+00:00
-- url     : https://prove2.me/theorems/9d4b8863-0f1d-42b8-bd19-1a6bb3f3ddfe
-- title:
--   Existence of an edge-maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_maximal_extension_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hDraw : HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X = W := by sorry
