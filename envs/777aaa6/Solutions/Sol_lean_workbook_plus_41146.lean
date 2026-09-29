-- Prove2me | solution 1 for lean_workbook_plus_41146
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:39:35.954587+00:00
-- url     : https://prove2.me/submissions/cf76571d-10f8-42c6-9f79-c9697194a9d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ → ℝ) (hp : p = (10^8 - 2009) / 10^9) : p (1/10) = (10^8 - 2009) / 10^9 := by
  (intros; simp_all)
