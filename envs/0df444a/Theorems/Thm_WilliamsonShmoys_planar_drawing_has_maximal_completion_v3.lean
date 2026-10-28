-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_completion_v3
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_completion_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:45:14.769994+00:00
-- url     : https://prove2.me/theorems/ef7530ea-a24a-40fa-92d7-3ae615caaafc
-- title:
--   Finite planar drawing has a maximal planar completion
-- statement:
--   Extend the graph to a graph on the same finite vertex type that contains every original edge and is maximal under adjacency inclusion among graphs satisfying the same planar drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_completion_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hNdraw : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      (∀ u v, N.Adj u v → M.Adj u v) ∧
      (HasPlanarDrawingOn M ∧
        ∀ M' : SimpleGraph V,
          (∀ u v, M.Adj u v → M'.Adj u v) →
          HasPlanarDrawingOn M' →
          ∀ u v, M'.Adj u v → M.Adj u v) := by sorry
