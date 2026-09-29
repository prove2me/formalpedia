-- Prove2me | Theorems.Thm_Erdos146_exp_mul_div_nat_succ_tendsto_atTop
-- name    : Erdos146.exp_mul_div_nat_succ_tendsto_atTop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:47:12.785894+00:00
-- url     : https://prove2.me/theorems/f17ff573-ad04-4e63-99ff-3a8eab6846c1
-- title:
--   An exponential growth limit
-- statement:
--   An elementary limit: an exponentially growing quantity divided by a linear one still tends to infinity. Used to run the asymptotics of Sections 7 and 8 in $m$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14747-L14788

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.exp_mul_div_nat_succ_tendsto_atTop
    (rate : ℝ) (hrate : 0 < rate) :
    Tendsto
      (fun dimension : ℕ =>
        Real.exp (rate * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ))
      atTop atTop := by sorry
