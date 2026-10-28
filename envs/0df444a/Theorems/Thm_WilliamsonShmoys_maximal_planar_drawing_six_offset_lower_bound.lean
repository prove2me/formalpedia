-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_six_offset_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_six_offset_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:29:42.645431+00:00
-- url     : https://prove2.me/theorems/e6900d01-e9d4-454e-a64f-eebc6e59faa2
-- title:
--   Maximal planar drawings attain the three-n-minus-six lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on a fixed finite vertex set of at least three vertices has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_six_offset_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hW : HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, HasPlanarDrawingOn X →
      (∀ u v, W.Adj u v → X.Adj u v) →
      ∀ u v, X.Adj u v → W.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by sorry
