-- Prove2me | solution 1 for lean_workbook_plus_16742
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:15.497157+00:00
-- url     : https://prove2.me/submissions/21780123-723a-41fe-8f0d-fbc4e047c276

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a k : ℤ) : (a - 2 + k) % 2 = (a - 2 - k) % 2 := by
  (intros; omega)
