-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- name    : WilliamsonShmoys.planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:14:20.413636+00:00
-- url     : https://prove2.me/theorems/918f6ef7-b742-4a7a-b6c7-f41fd05476c6
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable graph
-- statement:
--   Every drawable simple graph on a finite vertex type is contained in a drawable graph that is maximal under graph inclusion among drawable graphs on that same vertex type. This requires no lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_inclusion_maximal__p2m_bc67589b_3983_4963_b1d8_6aabd3b931c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
