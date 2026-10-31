-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:14:53.601828+00:00
-- url     : https://prove2.me/theorems/4c97134d-4021-4fb3-9ace-f88e43ef34b2
-- title:
--   Augmenting a drawable graph below the planar edge bound
-- statement:
--   Every drawable simple graph on at least three vertices with fewer than 3|V|−6 edges has a proper drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_augmentation__p2m_f5dec54e_fcbf_4bab_a342_af462107c326_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ H : SimpleGraph V, G ≤ H ∧ H ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
