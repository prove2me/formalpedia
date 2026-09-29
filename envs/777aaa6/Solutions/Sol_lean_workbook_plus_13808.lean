-- Prove2me | solution 1 for lean_workbook_plus_13808
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:35.378041+00:00
-- url     : https://prove2.me/submissions/8c73c33e-175e-4d1a-8876-e3abff98a973

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : Prop) (hab : a → b) (hbc : b → c) : a → c := by
  (intros; simp_all)
