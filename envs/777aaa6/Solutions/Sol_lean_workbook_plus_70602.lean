-- Prove2me | solution 1 for lean_workbook_plus_70602
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:24.195733+00:00
-- url     : https://prove2.me/submissions/578ea019-f7d1-4790-b740-c04de3e7a9dc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 1 / 2) :
  x ∈ Set.Ioo 0 (1 / 2) := by
  (intros; simp_all)
