-- Prove2me | solution 1 for lean_workbook_plus_812
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:00.755339+00:00
-- url     : https://prove2.me/submissions/799b33e8-6bc5-4a71-9bc9-be70b548a0fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (i j k : ℤ)
  (h₀ : 0 < i ∧ 0 < j ∧ 0 < k)
  (h₁ : i^2 + j^2 + k^2 = 2011)
  (h₂ : i + j + k = 0) :
  - Real.sqrt (3 * 2011) ≤ i + j + k ∧ i + j + k ≤ Real.sqrt (3 * 2011) := by
  (intros; omega)
