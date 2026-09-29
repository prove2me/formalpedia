-- Prove2me | solution 1 for Erdos146.exp_mul_div_nat_succ_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:24:29.275894+00:00
-- url     : https://prove2.me/submissions/3ddba27a-78a9-4bb9-95b9-057c25639179

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (rate : ℝ) (hrate : 0 < rate) :
    Tendsto
      (fun dimension : ℕ =>
        Real.exp (rate * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hquotient :
      Tendsto
        (fun dimension : ℕ =>
          Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ))
        atTop atTop := by
    have htendsto :=
      (tendsto_exp_mul_div_rpow_atTop 1 rate hrate).comp
        tendsto_natCast_atTop_atTop
    refine htendsto.congr' ?_
    filter_upwards [] with dimension
    simp [Function.comp_apply]
  have hhalf :
      Tendsto
        (fun dimension : ℕ =>
          (1 / 2 : ℝ) *
            (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)))
        atTop atTop :=
    hquotient.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [Filter.eventually_ge_atTop 1] with dimension hdimension
  have hpositive : 0 < (dimension : ℝ) := by
    exact_mod_cast (show 0 < dimension by omega)
  have hdimension_real : (1 : ℝ) ≤ (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (1 / 2 : ℝ) *
        (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)) =
      Real.exp (rate * (dimension : ℝ)) /
        (2 * (dimension : ℝ)) := by
        ring
    _ ≤ Real.exp (rate * (dimension : ℝ)) /
        ((dimension + 1 : ℕ) : ℝ) := by
      gcongr
      push_cast
      nlinarith
