-- Prove2me | solution 1 for lean_workbook_plus_62794
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:42.854229+00:00
-- url     : https://prove2.me/submissions/6014e436-3a2a-47f6-b3c3-03362f5de367

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℕ) : √(2000 * 2007 * 2008 * 2015 + 784) = 4030028 := by
  intros
  norm_num at *
