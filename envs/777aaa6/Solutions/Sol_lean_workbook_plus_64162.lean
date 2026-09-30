-- Prove2me | solution 1 for lean_workbook_plus_64162
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:31.736339+00:00
-- url     : https://prove2.me/submissions/23ce57ed-ea25-4041-b8d3-7f9c5328839c

import Mathlib
set_option autoImplicit false

theorem solution : Function.Bijective (fun x : ℝ => 1 / x)   := by
  simp only [one_div]
  exact inv_involutive.bijective

#print axioms solution
