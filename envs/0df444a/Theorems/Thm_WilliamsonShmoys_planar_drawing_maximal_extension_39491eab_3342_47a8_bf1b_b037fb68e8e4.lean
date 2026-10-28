-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:59:40.794408+00:00
-- url     : https://prove2.me/theorems/80f282ac-33d3-4bad-9a64-da22b51735c8
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   On a finite vertex type, extend a drawable graph to a drawable supergraph maximal among drawable supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_39491eab_3342_47a8_bf1b_b037fb68e8e4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
