-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_connected_supergraph_extension
-- name    : WilliamsonShmoys.planarDrawingOn_has_connected_supergraph_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T17:04:09.71932+00:00
-- url     : https://prove2.me/theorems/b575eb0b-092c-4d6e-a44b-f1a402a11573
-- title:
--   A drawable graph has a connected drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a connected drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_has_connected_supergraph_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ M : SimpleGraph V,
      J ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.Connected := by sorry
