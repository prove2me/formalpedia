-- Prove2me | solution 1 for lean_workbook_plus_56586
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:34.80276+00:00
-- url     : https://prove2.me/submissions/bc02439f-5be7-474f-9a90-51005651f985

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (G : Type*) [CommGroup G] (H : Subgroup G) : H.Normal := by
  (intros; constructor <;> norm_num)
