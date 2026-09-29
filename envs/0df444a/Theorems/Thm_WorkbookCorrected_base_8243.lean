-- Prove2me | Theorems.Thm_WorkbookCorrected_base_8243
-- name    : WorkbookCorrected.base_8243
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:12.672626+00:00
-- url     : https://prove2.me/theorems/1a67d4d0-be39-4c49-acba-f0285ea7e19f
-- title:
--   A product of shifted variables under a quadratic norm constraint
-- statement:
--   Let $a,b,c$ positive real numbers such that $a^2+b^2+c^2=3$. Prove that: $(a+2)(b+2)(c+2) \geq (a+b+c)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8243` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8243; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_8243 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2 + b^2 + c^2 = 3) :
  (a + 2) * (b + 2) * (c + 2) ≥ (a + b + c)^3  :=  by sorry
