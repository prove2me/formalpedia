-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_3daebd93
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_3daebd93
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:25:18.680135+00:00
-- url     : https://prove2.me/theorems/4eb19fe8-ed79-4758-a573-c720041754e6
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex set that is maximal under inclusion. Finiteness provides a maximal element among drawable supergraphs, and the input graph ensures that collection is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_3daebd93
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L := by sorry
