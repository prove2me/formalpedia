-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
-- name    : WilliamsonShmoys.maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:30:27.958518+00:00
-- url     : https://prove2.me/theorems/2279216b-323e-49ad-8df9-c00dc99288fc
-- title:
--   Extend a drawn graph to a maximal planar supergraph
-- statement:
--   Every graph with the specified planar drawing has a drawing-preserving supergraph on the same finite vertex type that is maximal under graph inclusion and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_same_vertices_c3c27980_9f1d_4b26_ac26_4100a7115914
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) ∧
      R.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
