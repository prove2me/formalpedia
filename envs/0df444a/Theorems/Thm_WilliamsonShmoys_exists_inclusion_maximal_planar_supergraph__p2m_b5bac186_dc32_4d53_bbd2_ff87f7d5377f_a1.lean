-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- name    : WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:33.817594+00:00
-- url     : https://prove2.me/theorems/27620d84-3d8e-4648-b1d5-eb1376ddda5d
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex set has a drawable supergraph that is maximal under edge inclusion among drawable graphs on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_b5bac186_dc32_4d53_bbd2_ff87f7d5377f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeFinset ⊆ H.edgeFinset ∧
      ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn K →
        H.edgeFinset ⊆ K.edgeFinset →
        K.edgeFinset ⊆ H.edgeFinset := by sorry
