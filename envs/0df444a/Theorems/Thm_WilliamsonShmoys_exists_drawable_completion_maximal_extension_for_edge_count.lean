-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_completion_maximal_extension_for_edge_count
-- name    : WilliamsonShmoys.exists_drawable_completion_maximal_extension_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:38:59.198572+00:00
-- url     : https://prove2.me/theorems/1d810a60-535c-4b22-8b0d-3bb52ceaab9e
-- title:
--   Maximal drawable extension for edge-count completion
-- statement:
--   Among drawable supergraphs of N on the finite vertex set V, choose one with the largest edge count. It is then inclusion-maximal among drawable supergraphs. The family is nonempty because it contains N. This isolates the finite maximality argument from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_completion_maximal_extension_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V, N ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
