-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487
-- name    : WilliamsonShmoys.planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:16:48.297842+00:00
-- url     : https://prove2.me/theorems/a358d772-4c14-4ce9-9dc7-9cac9e1128bc
-- title:
--   Edge-maximal planar extension on the fixed vertex set
-- statement:
--   Every graph with a drawing on a fixed finite vertex set has a supergraph admitting such a drawing that is maximal among planar supergraphs, and that contains at least as many edges as the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M) ∧
      N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
