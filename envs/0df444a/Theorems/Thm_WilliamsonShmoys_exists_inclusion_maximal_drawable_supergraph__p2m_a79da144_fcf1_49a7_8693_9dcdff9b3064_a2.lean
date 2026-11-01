-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:50.23964+00:00
-- url     : https://prove2.me/theorems/18f75cda-8dbf-4897-a58b-3181a91ee134
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on that same type. This isolates the finite maximality step from the geometric connectivity argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
