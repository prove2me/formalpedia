-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:39.147208+00:00
-- url     : https://prove2.me/theorems/0daa1692-c677-4e45-95d5-9be2e8b491a4
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_dee0ca40_6c9c_434d_8ef7_a3ab7a09b0fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hR : HasPlanarDrawingOn R) :
    ∃ M : SimpleGraph V, R ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
