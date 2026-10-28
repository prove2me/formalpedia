-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximalExtension
-- name    : WilliamsonShmoys.planarDrawing_maximalExtension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:19:30.77162+00:00
-- url     : https://prove2.me/theorems/62d77ddc-7891-4e21-9d95-9013d3150939
-- title:
--   A drawable graph has an edge-maximal drawable extension
-- statement:
--   Among the drawable supergraphs of a given drawable graph on a finite vertex type, there is one with maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_maximalExtension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q →
        P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
