-- Prove2me | Theorems.Thm_mme_log_series_bounds
-- name    : mme_log_series_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:32:30.4025+00:00
-- url     : https://prove2.me/theorems/ca4bf92e-83d0-4227-b932-43ccdd86929e
-- title:
--   Finite series enclose positive logarithms
-- statement:
--   A finite rational series and explicit remainder give lower and upper bounds for the real logarithm of every positive argument. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
open scoped BigOperators

theorem mme_log_series_bounds (x : ℝ) (hx : 0 < x) (n : ℕ) :
    let t := (x - 1) / (x + 1)
    let center := 2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2))
    center - error ≤ Real.log x ∧ Real.log x ≤ center + error := by sorry
