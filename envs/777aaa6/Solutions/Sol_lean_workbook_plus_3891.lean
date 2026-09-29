-- Prove2me | solution 1 for lean_workbook_plus_3891
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:27.204402+00:00
-- url     : https://prove2.me/submissions/a15ac663-f0a0-460b-b83f-52ae44511107

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (hx: 2^32+1 = 641*6700417): 2^32+1 = 641*6700417 := by
  norm_num
