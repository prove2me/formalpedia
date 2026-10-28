-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension_d6e88113
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension_d6e88113
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:31:07.583266+00:00
-- url     : https://prove2.me/theorems/e4e2c0d1-977b-449f-a5a3-a000748935c5
-- title:
--   Drawable triangulation extension
-- statement:
--   A connected drawable simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_extension_d6e88113
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
