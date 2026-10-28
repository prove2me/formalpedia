-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_exists_maximal_e9ce3df1_a197_4828_a24c_84c363604464
-- name    : WilliamsonShmoys.planar_completion_exists_maximal_e9ce3df1_a197_4828_a24c_84c363604464
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:59:50.696027+00:00
-- url     : https://prove2.me/theorems/7a6c4c00-1392-47b4-8c7b-7a9083418e1f
-- title:
--   A planar drawing has a maximal planar completion
-- statement:
--   Every planar graph on a finite vertex type has a planar supergraph that is maximal among planar supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_exists_maximal_e9ce3df1_a197_4828_a24c_84c363604464
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
