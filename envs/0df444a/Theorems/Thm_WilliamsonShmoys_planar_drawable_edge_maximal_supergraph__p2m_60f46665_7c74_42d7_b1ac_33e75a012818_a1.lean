-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- name    : WilliamsonShmoys.planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:00.253931+00:00
-- url     : https://prove2.me/theorems/a584cd68-9d17-4361-8b29-312b20e50fca
-- title:
--   Finite edge maximal planar extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_maximal_supergraph__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) := by
  sorry
