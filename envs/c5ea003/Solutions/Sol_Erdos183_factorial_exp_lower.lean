-- Prove2me | solution 1 for Erdos183.factorial_exp_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:23:59.97882+00:00
-- url     : https://prove2.me/submissions/26170ef4-f600-40e3-9c62-a5cec4bfb172

import Definitions.Def_erdos183_core
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Real.StarOrdered

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by
  have hsreal : (1 : ℝ) ≤ s := by
    exact_mod_cast hs
  have hradicand : (1 : ℝ) ≤ 2 * Real.pi * (s : ℝ) := by
    nlinarith [Real.pi_gt_three]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (s : ℝ)) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 * Real.pi * (s : ℝ) by positivity),
      Real.sqrt_nonneg (2 * Real.pi * (s : ℝ))]
  have hpower : 0 ≤ ((s : ℝ) / Real.exp 1) ^ s := by positivity
  calc
    ((s : ℝ) / Real.exp 1) ^ s ≤
        Real.sqrt (2 * Real.pi * (s : ℝ)) *
          ((s : ℝ) / Real.exp 1) ^ s := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hpower]
    _ ≤ (s.factorial : ℝ) := Stirling.le_factorial_stirling s
