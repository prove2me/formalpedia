-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- name    : WilliamsonShmoys.exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:19.718535+00:00
-- url     : https://prove2.me/theorems/36d82c5a-3675-4d25-ac4d-a1af43ddb7a1
-- title:
--   Existence of a maximum drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices whose edge count is maximum among its drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximum_drawable_supergraph__p2m_14ab409d_ba46_4520_b2b1_fae32ccc2155_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
          K.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
