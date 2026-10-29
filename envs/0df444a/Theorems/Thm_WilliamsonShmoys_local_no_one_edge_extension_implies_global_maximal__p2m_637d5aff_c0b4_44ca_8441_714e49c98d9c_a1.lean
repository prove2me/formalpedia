-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
-- name    : WilliamsonShmoys.local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:15:11.968694+00:00
-- url     : https://prove2.me/theorems/87998d71-f36e-4481-bd5e-a0624b01de15
-- title:
--   Local edge maximality implies global maximality
-- statement:
--   If a drawable finite simple graph has no drawable supergraph with exactly one additional edge, then it has no strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.local_no_one_edge_extension_implies_global_maximal__p2m_637d5aff_c0b4_44ca_8441_714e49c98d9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hNoOneEdgeExtension : ∀ L : SimpleGraph V, K ≤ L →
      L.edgeSet.ncard = K.edgeSet.ncard + 1 →
      WilliamsonShmoys.HasPlanarDrawingOn L → False) :
    ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → K = L := by sorry
