-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T14:35:00.242832+00:00
-- url     : https://prove2.me/submissions/1751c09b-eff0-4483-ac11-da11bcd80497

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

theorem solution (N : ℕ) :
    alexander (N + 1) = alexander N + (-1) ^ N * X ^ N := by
  simp [alexander, Finset.sum_range_succ]
