-- Prove2me | Theorems.Thm_exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- name    : exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:41.748221+00:00
-- url     : https://prove2.me/theorems/147a5295-4989-481d-a470-4dfaa73ce17a
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable extension on the same vertices that is maximal among drawable edge supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem exists_edge_maximal_drawable_extension__p2m_f8a91428_e2c7_41b2_beea_f098a7f4c4b7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset ⊆ K.edgeFinset := by
  sorry
