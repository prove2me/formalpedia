-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_to_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_extend_to_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:22:27.235984+00:00
-- url     : https://prove2.me/theorems/a66b30d0-4a80-4740-8f26-fe7b869979e8
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Among the planar supergraphs of the input graph on the same finite vertex type, choose one that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extend_to_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V] [DecidableEq V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
