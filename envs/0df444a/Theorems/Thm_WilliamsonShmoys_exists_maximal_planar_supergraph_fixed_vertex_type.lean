-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fixed_vertex_type
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertex_type
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:46:42.722987+00:00
-- url     : https://prove2.me/theorems/e01645af-b2fe-4e99-8b14-5b6442f47e5f
-- title:
--   Existence of a maximal planar supergraph on the fixed vertex type
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertex_type
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      W.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet := by
  sorry
