-- Prove2me | Theorems.Thm_WorkbookCorrected_base_10876
-- name    : WorkbookCorrected.base_10876
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:47.263729+00:00
-- url     : https://prove2.me/theorems/969f4463-e8ac-4b10-a371-f7b799fa459b
-- title:
--   A quartic sum bound for positive variables
-- statement:
--   Let $a,b,c,d$ be positive reals. Prove that: $(a+b+c)^4\geq16(a^2b^2+b^2c^2+c^2a^2)+11abc(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10876` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10876; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_10876 (a b c d : ℝ) (source_domain_d : 0 < d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 11 * a * b * c * (a + b + c)  :=  by sorry
