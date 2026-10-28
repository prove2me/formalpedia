-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_exists
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:55:25.28758+00:00
-- url     : https://prove2.me/theorems/7d9f9879-04bb-4b43-b3f2-091f5e9199bd
-- title:
--   Existence of an edge-maximal drawable extension
-- statement:
--   A connected drawable finite graph has a drawable supergraph on the same vertices that remains connected and has at least as many edges as every drawable supergraph of it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_exists
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      HasPlanarDrawingOn H ∧
      H.Connected ∧
      (∀ K : SimpleGraph V, HasPlanarDrawingOn K →
        (∀ u v, H.Adj u v → K.Adj u v) →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by
  sorry
