-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- name    : WilliamsonShmoys.planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:06:54.616011+00:00
-- url     : https://prove2.me/theorems/9c5450fd-f78e-4d07-b489-ede6a82645df
-- title:
--   Euler formula for connected drawable graphs
-- statement:
--   For a connected finite graph with a crossing-free drawing, the number of complementary faces satisfies Euler's equation. This child removes the Euler-characteristic calculation from the parent. A proof route is to derive a finite plane embedding from the drawing, define faces as the cycles of its dart permutation, and prove the Euler characteristic formula for a connected rotation system.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_euler_formula__p2m_ab3c4834_8b15_4a63_8fca_25572aaa5eac_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 := by sorry
