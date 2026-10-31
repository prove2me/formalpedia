-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:50:48.254754+00:00
-- url     : https://prove2.me/theorems/2c2fa59c-c2a7-475f-bc59-370cb8d75cfd
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a5cf4edc_e88b_40ef_a197_b0d2fda5eb44_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
