-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1
-- name    : WilliamsonShmoys.planar_extension_maximal__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:04:30.274439+00:00
-- url     : https://prove2.me/theorems/f3ed4a6c-9e75-406d-b8c8-602a8070aaab
-- title:
--   Extend a planar drawing to an inclusion-maximal planar graph
-- statement:
--   Every graph with a crossing-free drawing has a planar supergraph on the same vertices that is inclusion-maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_maximal__p2m_21bb6f97_2922_436c_8d92_71f0b7399afd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      K.edgeSet ⊆ T.edgeSet ∧
      ∀ U : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn U →
        T.edgeSet ⊆ U.edgeSet → U = T := by
  sorry
