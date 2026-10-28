-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_cd4931de_38bf_49be_8f7a_54b333eaee7b
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cd4931de_38bf_49be_8f7a_54b333eaee7b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:08:50.562413+00:00
-- url     : https://prove2.me/theorems/d75feba6-a6df-4c8f-994f-406fec4f6ace
-- title:
--   A drawable supergraph maximal by edge inclusion exists
-- statement:
--   On a finite vertex type, any drawable graph has a drawable supergraph containing its edges that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_cd4931de_38bf_49be_8f7a_54b333eaee7b
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V,
      HasPlanarDrawingOn X ∧
      (∀ u v, W.Adj u v → X.Adj u v) ∧
      (∀ Y : SimpleGraph V, HasPlanarDrawingOn Y →
        (∀ u v, W.Adj u v → Y.Adj u v) →
        ∀ u v, Y.Adj u v → X.Adj u v) := by sorry
