-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_d6e88113
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension_d6e88113
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:16:20.293608+00:00
-- url     : https://prove2.me/theorems/6517db74-e2d3-4878-8048-d15eed84ba1c
-- title:
--   Maximal drawable extension on a fixed vertex set
-- statement:
--   Every connected drawable graph on a finite ordered vertex type has a connected drawable supergraph on that same vertex type that is maximal under drawable edge inclusion. Finite maximization over the supergraphs of H gives the extension; connectivity is preserved by edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_extension_d6e88113
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧ K.Connected ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L → K ≤ L → L ≤ K) := by
  sorry
