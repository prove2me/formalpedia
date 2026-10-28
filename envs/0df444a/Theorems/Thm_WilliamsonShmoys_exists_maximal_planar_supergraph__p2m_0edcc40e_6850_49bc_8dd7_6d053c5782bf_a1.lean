-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:46:57.794001+00:00
-- url     : https://prove2.me/theorems/ff3915fc-abca-4176-9ba9-489c8aaa0e6f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices to which no missing edge can be added while preserving drawability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_0edcc40e_6850_49bc_8dd7_6d053c5782bf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V) (hS : HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ u v, S.Adj u v → T.Adj u v) ∧
      HasPlanarDrawingOn T ∧
      (∀ u v, u ≠ v → ¬ T.Adj u v →
        ¬ ∃ U : SimpleGraph V,
          (∀ x y, T.Adj x y → U.Adj x y) ∧
          HasPlanarDrawingOn U ∧ U.Adj u v) := by sorry
