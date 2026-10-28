-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:51:59.979443+00:00
-- url     : https://prove2.me/theorems/ebda8d02-837f-45b7-9a60-6b98dff07a17
-- title:
--   Maximal planar supergraph on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing on at least three vertices is contained in a planar supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_88c6cb28_d980_4ba8_aca2_3c8dda9dfd09
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
