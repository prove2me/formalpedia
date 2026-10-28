-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_maximumExtension
-- name    : WilliamsonShmoys.planarDrawing_maximumExtension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:02:01.114666+00:00
-- url     : https://prove2.me/theorems/c95b1250-db55-4204-b252-9c569da5472b
-- title:
--   A drawable graph has a maximum-edge drawable extension
-- statement:
--   Among drawable supergraphs of a given drawable graph on a finite vertex type, one has maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_maximumExtension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, N ≤ Q → HasPlanarDrawingOn Q →
        Q.edgeSet.ncard ≤ P.edgeSet.ncard := by sorry
