-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:04:59.198326+00:00
-- url     : https://prove2.me/theorems/4f3ad13b-2b09-4093-b783-79baa460e645
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable supergraphs. This removes the extension-selection step from the parent. A proof can choose a drawable supergraph with maximum edge count from the finite set of possible edge sets; its edge maximality gives the stated mutual inclusion condition for every drawable extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      ∀ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn N →
        M.edgeFinset ⊆ N.edgeFinset → N.edgeFinset ⊆ M.edgeFinset := by sorry
