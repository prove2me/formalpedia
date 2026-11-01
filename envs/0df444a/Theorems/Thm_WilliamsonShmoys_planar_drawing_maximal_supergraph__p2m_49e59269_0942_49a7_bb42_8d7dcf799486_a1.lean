-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:41.322239+00:00
-- url     : https://prove2.me/theorems/f94053f9-aa1c-4659-90f3-4794e32e1f9a
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph U, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L := by
  sorry
