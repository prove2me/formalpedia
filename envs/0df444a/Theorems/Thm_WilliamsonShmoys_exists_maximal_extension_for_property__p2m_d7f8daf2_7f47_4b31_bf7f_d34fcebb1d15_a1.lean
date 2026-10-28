-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_for_property__p2m_d7f8daf2_7f47_4b31_bf7f_d34fcebb1d15_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_for_property__p2m_d7f8daf2_7f47_4b31_bf7f_d34fcebb1d15_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:00:20.200718+00:00
-- url     : https://prove2.me/theorems/51d6676a-8959-40a5-852d-713ddee3d211
-- title:
--   Finite maximal extension for an arbitrary graph property
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has an extension satisfying it that is maximal among all such extensions. No heredity assumption on the predicate is required.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_extension_for_property__p2m_d7f8daf2_7f47_4b31_bf7f_d34fcebb1d15_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧
      P L ∧
      ∀ M : SimpleGraph V,
        L ≤ M →
        P M →
        M = L := by sorry
