-- Prove2me | solution 1 for lean_workbook_plus_24931
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:29.933323+00:00
-- url     : https://prove2.me/submissions/d12b5fb6-7669-4369-8aef-765c61dee521

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {f : ℝ → ℝ}
  (hf : ∀ x y, |f x - f y| < |x - y|)
  (x y : ℝ)
  (hxy : x ≠ y) :
  |f x - f y| < |x - y| := by
  (intros; simp_all)
