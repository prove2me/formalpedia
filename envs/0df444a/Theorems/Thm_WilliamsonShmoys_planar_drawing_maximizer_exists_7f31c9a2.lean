-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximizer_exists_7f31c9a2
-- name    : WilliamsonShmoys.planar_drawing_maximizer_exists_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:41:33.211556+00:00
-- url     : https://prove2.me/theorems/d87d5ec8-7b54-4bf5-94b5-1a4304032921
-- title:
--   A finite planar graph has a maximum drawable supergraph
-- statement:
--   Among the drawable simple graphs on the same finite vertex type that contain K, one has maximum edge count. Finiteness of the possible simple graphs and the witness K provide an independent proof route.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximizer_exists_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V,
        (∀ u v, K.Adj u v → G.Adj u v) →
        HasPlanarDrawingOn G →
        G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
