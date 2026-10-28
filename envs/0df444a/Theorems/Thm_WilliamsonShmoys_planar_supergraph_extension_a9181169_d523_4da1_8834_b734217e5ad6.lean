-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6
-- name    : WilliamsonShmoys.planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:36:54.302614+00:00
-- url     : https://prove2.me/theorems/bf51dfe8-1a20-499b-a886-3a75f4fd5ee3
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every graph with a planar drawing on the finite vertex type is contained in a planar graph on the same vertices that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_extension_a9181169_d523_4da1_8834_b734217e5ad6
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V, HasPlanarDrawingOn T ∧
      (∀ u v, G.Adj u v → T.Adj u v) ∧
      (∀ U : SimpleGraph V, HasPlanarDrawingOn U →
        (∀ u v, T.Adj u v → U.Adj u v) → U = T) := by sorry
