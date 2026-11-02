-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
-- name    : WilliamsonShmoys.finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:35:33.193651+00:00
-- url     : https://prove2.me/theorems/fcf3c6ea-494e-464f-809a-ef21a5f75568
-- title:
--   Finite simple graph families have an inclusion-maximal member
-- statement:
--   For a finite linearly ordered vertex type, every nonempty family of simple graphs on that type has a member maximal under graph inclusion. This packages the finite maximization step; the target applies it to drawable supergraphs of H. The boundary case of an empty family is excluded by hP, while the single-member case is immediate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_simpleGraph_has_maximal_element__p2m_21abd8cf_71a5_4301_9a22_948ffb9f2078_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hP : ∃ K : SimpleGraph V, P K) :
    ∃ K : SimpleGraph V, P K ∧
      ∀ L : SimpleGraph V, P L → K ≤ L → L ≤ K := by sorry
