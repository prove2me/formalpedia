-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_v2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_finite_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:12:44.449016+00:00
-- url     : https://prove2.me/theorems/4ad49820-bf27-4706-81d9-b2b55019797e
-- title:
--   Finite maximal planar supergraph on the same vertices
-- statement:
--   A connected planar drawing on a finite vertex type has a connected planar supergraph on the same vertices that is maximal among planar supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_finite_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.Connected ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
