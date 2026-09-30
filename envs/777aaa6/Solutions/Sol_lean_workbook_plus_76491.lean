-- Prove2me | solution 1 for lean_workbook_plus_76491
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:23:19.365318+00:00
-- url     : https://prove2.me/submissions/dd7ec448-ed48-4465-a19d-96f71599f282

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a < b + c) : a / (1 + a) < b / (1 + b) + c / (1 + c) := by
  have hda : 0 < 1 + a := by positivity
  have hdb : 0 < 1 + b := by positivity
  have hdc : 0 < 1 + c := by positivity
  have hds : 0 < 1 + b + c := by positivity
  have hmono : a / (1 + a) < (b + c) / (1 + b + c) := by
    apply (div_lt_div_iff₀ hda hds).mpr
    nlinarith
  have hleft : b / (1 + b + c) < b / (1 + b) := by
    apply (div_lt_div_iff₀ hds hdb).mpr
    nlinarith [mul_pos hb hc]
  have hright : c / (1 + b + c) < c / (1 + c) := by
    apply (div_lt_div_iff₀ hds hdc).mpr
    nlinarith [mul_pos hb hc]
  calc
    a / (1 + a) < (b + c) / (1 + b + c) := hmono
    _ = b / (1 + b + c) + c / (1 + b + c) := add_div _ _ _
    _ < b / (1 + b) + c / (1 + c) := add_lt_add hleft hright

#print axioms solution
