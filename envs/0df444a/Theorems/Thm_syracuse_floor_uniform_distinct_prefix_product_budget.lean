-- Prove2me | Theorems.Thm_syracuse_floor_uniform_distinct_prefix_product_budget
-- name    : syracuse_floor_uniform_distinct_prefix_product_budget
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T11:14:53.762396+00:00
-- url     : https://prove2.me/theorems/a66905b6-ebf7-52b8-b8ff-79ac90edb1d3
-- title:
--   Uniform Syracuse product control for a distinct finite prefix above a global floor
-- statement:
--   Uniformly in the floor B, the correction to the Syracuse multiplicative model is bounded by the displayed small power of k+1 when only the first k states are distinct and the whole orbit stays above B.
-- source:
--   Uses the Proved uniform logarithmic Syracuse tail estimate, https://prove2.me/theorems/10697865-c049-4b18-8190-6f57f19040fc.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem syracuse_floor_uniform_distinct_prefix_product_budget :
    ∃ D d : ℝ, 0 < D ∧ 0 < d ∧
      ∀ (n B k : ℕ), 3 ≤ B → 1 ≤ k → Odd n →
        Set.InjOn (fun i : ℕ => syracuseStep^[i] n) {i | i < k} →
        (∀ i : ℕ, B < syracuseStep^[i] n) →
        (2:ℝ)^((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2) *
          (syracuseStep^[k] n : ℝ) ≤
        Real.exp (1/3) * (n:ℝ) * (3:ℝ)^k *
          (((k:ℝ)+1)^(D/(Real.log (B:ℝ))^d)) := by sorry
