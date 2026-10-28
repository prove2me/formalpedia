-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:59:53.979806+00:00
-- url     : https://prove2.me/theorems/a2efa62b-0ddf-4593-9d8a-83f37c3d3cfc
-- title:
--   A drawable graph has a drawable edge-maximal extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that has no drawable strict supergraph. Choose a maximum-edge drawable supergraph among the finite set of supergraphs containing the input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_96e18dc0_fcd2_4f0d_85b5_0dc02d147dce
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn J →
        J.edgeSet = H.edgeSet := by sorry
