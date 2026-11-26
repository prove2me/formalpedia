-- Prove2me | Theorems.Thm_syracuse_small_valuation_deficit_times_log_density_zero
-- name    : syracuse_small_valuation_deficit_times_log_density_zero
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:59:55.864899+00:00
-- url     : https://prove2.me/theorems/fcdc32f3-87a1-475e-b481-c6fb1d728a97
-- title:
--   Small valuation deficits have logarithmic density zero on an injective Syracuse orbit
-- statement:
--   For an injective Syracuse orbit from an odd starting value, write A(k) for the sum of the first k two-adic valuations. For every fixed natural D, the times k such that 3^(6k) is at most D times 2^(6A(k)) times (k+1)^5 have logarithmic density zero with weights 1/(k+1).
-- source:
--   Combines the verified uniform logarithmic tail bound in Tao’s almost-bounded orbit method with a product estimate for distinct odd orbit states.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter
open scoped Topology BigOperators

theorem syracuse_small_valuation_deficit_times_log_density_zero (n D : ℕ)
    (hodd : n % 2 = 1) (hinj : Function.Injective (fun i : ℕ => syracuseStep^[i] n)) :
    Tendsto (fun L : ℕ =>
      (∑ k ∈ Finset.range L,
        if 3^(6*k) ≤ D * 2^(6*((Finset.range k).sum fun i => (3*syracuseStep^[i] n+1).factorization 2)) *
          (k+1)^5 then (1:ℝ)/((k:ℝ)+1) else 0) / Real.log ((L:ℝ)+1)) atTop (𝓝 0) := by sorry
