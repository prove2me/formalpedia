-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_v3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_v3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:47:18.16883+00:00
-- url     : https://prove2.me/theorems/65d8859f-f83e-4a3a-8eb8-9f98d5510cdc
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A graph maximal under adjacency inclusion among graphs satisfying the given drawing predicate has exactly `3 * |V| - 6` edges when it has at least three vertices. Prove this by deriving connectivity and triangular faces, then applying Euler’s formula and face-edge incidence counting, with the three-vertex boundary handled explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hmax : HasPlanarDrawingOn M ∧
      ∀ M' : SimpleGraph V,
        (∀ u v, M.Adj u v → M'.Adj u v) →
        HasPlanarDrawingOn M' →
        ∀ u v, M'.Adj u v → M.Adj u v)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
