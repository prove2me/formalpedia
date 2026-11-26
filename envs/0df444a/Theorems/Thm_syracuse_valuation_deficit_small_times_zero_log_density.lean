-- Prove2me | Theorems.Thm_syracuse_valuation_deficit_small_times_zero_log_density
-- name    : syracuse_valuation_deficit_small_times_zero_log_density
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:11:06.226799+00:00
-- url     : https://prove2.me/theorems/5a8a91a6-67d8-4250-8f30-6a69b4a61deb
-- title:
--   Valuation deficits with any coefficient below one have logarithmic density zero
-- statement:
--   Let x(k) be a positive-start Syracuse orbit with no repeated states, and A(k) the first k valuations summed. For any real q<1 and any fixed real D, the times k>0 for which 3^k ≤ D·2^A(k)·(k+1)^q have logarithmic density zero with weights 1/(k+1).
-- source:
--   Uses the verified uniform logarithmic tail bound behind Tao’s Collatz theorem to obtain subpower growth of the affine correction along an injective orbit.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter
open scoped Topology BigOperators

theorem syracuse_valuation_deficit_small_times_zero_log_density
    (n : ℕ) (hn : 0 < n) (q D : ℝ) (hq : q < 1)
    (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    Tendsto (fun L : ℕ =>
      (∑ k ∈ Finset.range L,
        if 0 < k ∧ (3:ℝ)^k ≤ D*(2:ℝ)^((Finset.range k).sum fun i =>
          (3*syracuseStep^[i] n+1).factorization 2)*(((k:ℝ)+1)^q)
        then (1:ℝ)/((k:ℝ)+1) else 0) / Real.log ((L:ℝ)+1)) atTop (𝓝 0) := by sorry
