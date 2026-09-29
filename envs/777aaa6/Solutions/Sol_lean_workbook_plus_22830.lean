-- Prove2me | solution 1 for lean_workbook_plus_22830
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:05.787284+00:00
-- url     : https://prove2.me/submissions/513a6f29-ca1e-4a68-8a07-0cec5b68e3a9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p := by
  (intros; simp_all)
