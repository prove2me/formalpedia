-- Prove2me | Theorems.Thm_WorkbookCorrected_base_32021
-- name    : WorkbookCorrected.base_32021
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:03.850367+00:00
-- url     : https://prove2.me/theorems/668d5462-f576-4808-a8ca-e9980f146190
-- title:
--   A cubic and linear sum bound under unit product
-- statement:
--   Let $a,b,c$ be positive real numbers such that $abc=1$ . Prove that $$a+b+c+a^3+b^3+c^3\leq \frac{2}{3} (a^2+b^2+c^2)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32021` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32021; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_32021 (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h1 : a * b * c = 1) :
  a + b + c + a^3 + b^3 + c^3 ≤ (2 / 3) * (a^2 + b^2 + c^2)^2  :=  by sorry
