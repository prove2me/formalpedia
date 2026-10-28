-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:14:16.378541+00:00
-- url     : https://prove2.me/theorems/d153d180-b859-46b9-b8b4-f659b462f8ce
-- title:
--   A maximal drawable graph has the maximal planar edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge inclusion has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_aca21fa1_3086c322_8519_4d73_8f33_f085f9c7277b
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hMax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) → X = W)
    (hCard : 3 ≤ Fintype.card V) :
    (W.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
