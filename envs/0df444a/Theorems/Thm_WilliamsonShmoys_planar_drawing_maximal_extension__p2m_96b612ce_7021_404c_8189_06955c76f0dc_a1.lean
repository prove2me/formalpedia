-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:47:08.253995+00:00
-- url     : https://prove2.me/theorems/d7f8daf2-7f47-4b31-bf7f-d34fcebb1d15
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type. Choose a drawable supergraph maximizing its finite edge count; any strict drawable extension would contradict maximality. This removes the finite-choice step from the parent. The remaining core is the separate planar edge-count bound for maximal drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M = L := by sorry
