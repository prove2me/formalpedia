-- Prove2me | Theorems.Thm_lean_workbook_plus_15636
-- name    : lean_workbook_plus_15636
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/eef93b49-848a-45c2-878d-66615ca2dd9b
-- statement:
--   Let $a,b,c \ge 0$ . Prove that: $a^4+b^4+c^4 \ge abc(a+b+c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15636 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c)   :=  by sorry
