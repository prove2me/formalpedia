-- Prove2me | Theorems.Thm_syracuse_floor_uniform_product_budget
-- name    : syracuse_floor_uniform_product_budget
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:13:28.202865+00:00
-- url     : https://prove2.me/theorems/986b0a79-913d-5369-bd53-a8450caa1f3a
-- title:
--   Uniform Syracuse affine product bound at a fixed orbit floor
-- statement:
--   There are positive universal real constants D,d such that the following holds. If an injective Syracuse orbit from an odd start n stays strictly above B≥3, then for each k≥1 its endpoint times 2 raised to the cumulative valuation A(k) is at most exp(1/3)·n·3^k·(k+1)^(D/(log B)^d).
-- source:
--   Uses the Prove2Me uniform logarithmic tail bound underlying Tao’s almost-boundedness theorem, applied to an injective orbit that stays above the given floor.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

theorem syracuse_floor_uniform_product_budget :
    ∃ D d : ℝ, 0 < D ∧ 0 < d ∧
      ∀ (n B k : ℕ), 3 ≤ B → 1 ≤ k → Odd n →
        Function.Injective (fun i : ℕ => syracuseStep^[i] n) →
        (∀ i : ℕ, B < syracuseStep^[i] n) →
        (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
          (syracuseStep^[k] n : ℝ) ≤
        Real.exp (1/3) * (n:ℝ) * (3:ℝ)^k *
          (((k:ℝ)+1)^(D/(Real.log (B:ℝ))^d)) := by sorry
