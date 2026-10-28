-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_for_4be75fe8
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_for_4be75fe8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:41:59.937275+00:00
-- url     : https://prove2.me/theorems/64a89bfb-6c8f-4945-88a5-6dade38543d3
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_for_4be75fe8
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V, M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = M := by sorry
