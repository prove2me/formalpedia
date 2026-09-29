-- Prove2me | Theorems.Thm_mme_dyadic_log_series_bounds
-- name    : mme_dyadic_log_series_bounds
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:42:14.448701+00:00
-- url     : https://prove2.me/theorems/8d29a11c-3efb-4d29-bd64-905d1b544338
-- title:
--   Integer dyadic scaling sharpens logarithm enclosures
-- statement:
--   Integer powers of two move small probabilities and large dual weights near one. Finite series for the scaled argument and log two give explicit rational centers and errors for the original logarithm. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_log_series_bounds
open scoped BigOperators

theorem mme_dyadic_log_series_bounds (x : ℝ) (hx : 0 < x) (k : ℤ) (n : ℕ) :
    let t := ((2 : ℝ) ^ k * x - 1) / ((2 : ℝ) ^ k * x + 1)
    let twoCenter := 2 * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1)
    let twoError := 2 * ((1 / 3 : ℝ) ^ (2 * n + 1) / (1 - (1 / 3 : ℝ) ^ 2))
    let center := (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)) -
      (k : ℝ) * twoCenter
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2)) + |(k : ℝ)| * twoError
    center - error ≤ Real.log x ∧ Real.log x ≤ center + error := by sorry
