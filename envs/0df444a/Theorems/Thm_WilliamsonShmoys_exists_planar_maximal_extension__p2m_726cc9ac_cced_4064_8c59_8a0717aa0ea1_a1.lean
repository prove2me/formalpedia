-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1
-- name    : WilliamsonShmoys.exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:49:15.907999+00:00
-- url     : https://prove2.me/theorems/fb127044-7eaa-4a6b-8f9a-9285d89f3ac4
-- title:
--   Planar supergraph maximizing edge count
-- statement:
--   Every drawn graph on a finite vertex type has a drawn supergraph containing its edges whose edge count is at least that of every drawn supergraph of the chosen graph, and at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_maximal_extension__p2m_726cc9ac_cced_4064_8c59_8a0717aa0ea1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
