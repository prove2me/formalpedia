-- Prove2me | Theorems.Thm_lean_workbook_plus_68393
-- name    : lean_workbook_plus_68393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/14597e31-731a-45a3-9622-2102377c0b4b
-- statement:
--   Find the value of $abc$ where $a = \frac{1999\cdot1999-1999}{1998\cdot1998+1998}$, $b = \frac{2000\cdot2000-2000}{1999\cdot1999+1999}$, and $c = \frac{2001\cdot2001-2001}{2000\cdot2000+2000}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68393 (a b c : ℚ) (ha : a = (1999 * 1999 - 1999) / (1998 * 1998 + 1998)) (hb : b = (2000 * 2000 - 2000) / (1999 * 1999 + 1999)) (hc : c = (2001 * 2001 - 2001) / (2000 * 2000 + 2000)) : a * b * c = 1   :=  by sorry
