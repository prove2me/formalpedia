-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_exists_maximal_supergraph
-- name    : WilliamsonShmoys.planar_drawing_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:19:21.868486+00:00
-- url     : https://prove2.me/theorems/6f165525-180a-4c1d-adf9-1d1944b7d442
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with a planar drawing is contained in a same-vertex-set planar graph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  sorry
